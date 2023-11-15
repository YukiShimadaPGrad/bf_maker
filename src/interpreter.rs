//! BFの処理系

use std::{
    collections::VecDeque,
    io::{stdout, Write},
};

use crate::bit_flag::{BitFlag, U8Flag};

/// BFのデフォルトのメモリサイズ
pub const BF_MEM_SIZE: usize = 30000;

/// BFの命令の種類数
pub const BF_OP_KINDS: usize = 8;

/// BFの命令の種類
#[derive(Clone, Copy, Hash, Debug, PartialEq, Eq)]
pub enum Token {
    Inc,
    Dec,
    PtrInc,
    PtrDec,
    LoopBegin,
    LoopEnd,
    In,
    Out,
}

pub const TOKEN_ENUMS: [Token; BF_OP_KINDS] = [
    Token::Inc,
    Token::Dec,
    Token::PtrInc,
    Token::PtrDec,
    Token::LoopBegin,
    Token::LoopEnd,
    Token::In,
    Token::Out,
];

/// [Parser] の作成中に起こりうるエラー
#[derive(Clone, Copy, Hash, Debug)]
pub enum ParserBuildError {
    HasEmptyOps,
    HasDuplicatedOps,
}

/// 好きな文字列を、BFプログラムから最長一致するものを探し、BFのひとつの命令に変換する
#[derive(Clone, Debug)]
pub struct Parser {
    tokens: [String; BF_OP_KINDS],
    char_count_max: usize,
}

/// 好きな文字列をひとつのBFの命令に変換するパーサ
impl Parser {
    pub fn new(tokens: [String; BF_OP_KINDS]) -> Result<Self, ParserBuildError> {
        {
            let mut unique_tokens = tokens
                .iter()
                .filter(|v| !v.is_empty())
                .collect::<Vec<&String>>();
            if unique_tokens.len() != BF_OP_KINDS {
                return Err(ParserBuildError::HasEmptyOps);
            }
            unique_tokens.dedup();
            if unique_tokens.len() != tokens.len() {
                return Err(ParserBuildError::HasDuplicatedOps);
            }
        }
        let mut parser = Parser {
            tokens: Default::default(),
            char_count_max: tokens.iter().map(|v| v.chars().count()).max().unwrap(), // 要素数が決まっているのでmax()がNoneになり得ない
        };
        parser
            .tokens
            .iter_mut()
            .enumerate()
            .for_each(|(i, v)| *v = tokens[i].to_string());
        Ok(parser)
    }

    /// BFの演算子に変換する処理。 `program` の先頭から最長一致探索し、見つかった場合はBFの命令と読んだ文字数を返す。
    fn parse_word(&self, program: &str) -> Option<(Token, usize)> {
        let mut match_flag = U8Flag::new(0xff);
        let mut guaranteed_flag = U8Flag::new(0);
        for i in 0..usize::min(self.char_count_max, program.chars().count()) {
            for j in 0..BF_OP_KINDS {
                if match_flag.get(j) {
                    let op_char_len = self.tokens[j].chars().count();
                    let (op_last, op_char) = self.tokens[j].char_indices().nth(i).unwrap();
                    let (pg_last, pg_char) = program.char_indices().nth(i).unwrap();
                    if i + 1 < op_char_len {
                        if self.tokens[j][0..op_last + op_char.len_utf8()]
                            != program[0..pg_last + pg_char.len_utf8()]
                        {
                            match_flag = match_flag.off(j);
                        }
                    } else if i + 1 == op_char_len {
                        match_flag = match_flag.off(j);
                        if self.tokens[j][0..op_last + op_char.len_utf8()]
                            == program[0..pg_last + pg_char.len_utf8()]
                        {
                            guaranteed_flag = U8Flag::new(0).on(j);
                        }
                    }
                }
            }
            if !match_flag.any() {
                break;
            }
        }
        if guaranteed_flag.any() {
            let i_op = guaranteed_flag.get_raw().ilog2() as usize;
            Some((TOKEN_ENUMS[i_op], self.tokens[i_op].chars().count()))
        } else {
            None
        }
    }

    pub fn get_op_str(&self, token: Token) -> &str {
        &self.tokens[token as usize]
    }
}

impl Default for Parser {
    fn default() -> Self {
        Self::new([
            "+".to_string(),
            "-".to_string(),
            ">".to_string(),
            "<".to_string(),
            "[".to_string(),
            "]".to_string(),
            ",".to_string(),
            ".".to_string(),
        ])
        .unwrap()
    }
}

/// BFプログラムを実行する
/// - `program` BFプログラム
/// - `parser` `program` から命令語を取り出す
/// - `mem_bytes` BF処理系のメモリサイズ
pub fn interpret(program: &str, parser: &Parser, mem_bytes: usize) -> Result<(), String> {
    let mut memory = vec![0u8; mem_bytes]; //BFのメモリ
    let mut ptr = 0usize; //BFのポインタ

    let mut pc = 0usize; //programの0文字目を基準とした実行位置
    let mut loop_pos_stack = Vec::<usize>::new(); //"["によるループ開始地点の次の命令の位置記録用
    let mut input_buf = VecDeque::<u8>::new(); //入力文字列
    let mut output_buf = Vec::<u8>::new(); //出力文字列

    while pc < program.len() {
        if let Some((op, op_len)) = parser.parse_word(&program[pc..]) {
            let mut inc_pc_flag = true;
            match op {
                Token::Inc => {
                    if ptr < mem_bytes {
                        memory[ptr] += 1;
                    } else {
                        println_u8(&mut output_buf);
                        return Err(make_bad_access_err_string(pc, ptr));
                    }
                }
                Token::Dec => {
                    if ptr < mem_bytes {
                        memory[ptr] -= 1;
                    } else {
                        println_u8(&mut output_buf);
                        return Err(make_bad_access_err_string(pc, ptr));
                    }
                }
                Token::PtrInc => ptr += 1,
                Token::PtrDec => ptr -= 1,
                Token::LoopBegin => {
                    if mem_bytes <= ptr {
                        println_u8(&mut output_buf);
                        return Err(make_bad_access_err_string(pc, ptr));
                    }
                    // loop_pos_stack.push(pc + op_len);
                    loop_pos_stack.push(pc + get_skip_bytes(&program[pc..], op_len).unwrap());
                    if memory[ptr] == 0 {
                        //対応する']'の次まで飛ばす
                        let depth = loop_pos_stack.len();
                        while pc < program.len() {
                            if let Some((op, op_len)) = parser.parse_word(&program[pc..]) {
                                match op {
                                    // Token::LoopBegin => loop_pos_stack.push(pc + op_len),
                                    Token::LoopBegin => loop_pos_stack.push(pc + get_skip_bytes(&program[pc..], op_len).unwrap()),
                                    Token::LoopEnd => {
                                        loop_pos_stack.pop();
                                        if depth == loop_pos_stack.len() + 1 {
                                            pc += op_len;
                                            break;
                                        }
                                    }
                                    _ => {}
                                }
                                // pc += op_len;
                                pc += get_skip_bytes(&program[pc..], op_len).unwrap();
                            } else {
                                // pc += 1;
                                pc += get_skip_bytes(&program[pc..], 1).unwrap();
                            }
                        }
                        inc_pc_flag = false;
                    }
                }
                Token::LoopEnd => {
                    if mem_bytes <= ptr {
                        println_u8(&mut output_buf);
                        return Err(make_bad_access_err_string(pc, ptr));
                    }
                    if memory[ptr] == 0 {
                        loop_pos_stack.pop();
                    } else {
                        if let Some(pos) = loop_pos_stack.last() {
                            pc = *pos;
                            inc_pc_flag = false;
                        } else {
                            println_u8(&mut output_buf);
                            return Err(make_error_string(pc, "対応するループの開始点がないぞ"));
                        }
                    }
                }
                Token::In => {
                    println_u8(&mut output_buf); //溜まっている出力をここで流す
                    while input_buf.is_empty() {
                        print!("何か入力してね->");
                        stdout().flush().expect("標準入力のflushに失敗");
                        input_buf.append(&mut (read_stdin_to_u8vec().into()));
                    }
                    if ptr < mem_bytes {
                        memory[ptr] = input_buf.pop_front().unwrap();
                    } else {
                        return Err(make_bad_access_err_string(pc, ptr));
                    }
                }
                Token::Out => {
                    if ptr < mem_bytes {
                        output_buf.push(memory[ptr]); //ここではまだ標準出力に流さない
                    } else {
                        println_u8(&mut output_buf);
                        return Err(make_bad_access_err_string(pc, ptr));
                    }
                }
            }
            if inc_pc_flag {
                // pc += op_len;
                pc += get_skip_bytes(&program[pc..], op_len).unwrap();
            }
        } else {
            // pc += 1;
            pc += get_skip_bytes(&program[pc..], 1).unwrap();
        }
    }
    if !output_buf.is_empty() {
        println_u8(&mut output_buf);
    }
    Ok(())
}

/// 純粋なBFプログラムをユーザ定義命令語で置換する
/// `program` BFプログラム
/// `parser` ユーザ定義の命令語への変換器
pub fn convert(program: &str, parser: &Parser) -> String {
    let mut pc = 0usize; //programの0文字目を基準とした実行位置
    let mut converted = Vec::<Token>::with_capacity(program.len());
    let bf_parser = Parser::default();
    while pc < program.len() {
        if let Some((op, op_len)) = bf_parser.parse_word(&program[pc..]) {
            converted.push(op);
            pc += get_skip_bytes(&program[pc..], op_len).unwrap();
        } else {
            pc += get_skip_bytes(&program[pc..], 1).unwrap();
        }
    }
    let mut program_conv = String::new();
    for op in converted {
        program_conv.push_str(parser.get_op_str(op));
    }
    program_conv
}

fn get_skip_bytes(s: &str, char_num: usize) -> Option<usize> {
    // s.char_indices().nth(char_num).unwrap().0
    // let (i, ch) = s.char_indices().nth(char_num - 1)?;
    // Some(i + ch.len_utf8())

    let (i, ch) = s.char_indices().nth(char_num - 1)?;
    Some(s[0..i].len() + ch.len_utf8())
}

fn make_error_string(pc: usize, msg: &str) -> String {
    // TODO 現在のアドレス付近のメモリを表示
    return format!(
        r#"Your brain was f*cked !!!
    実行場所: {pc}文字目
    {msg}
    "#
    );
}

fn make_bad_access_err_string(pc: usize, ptr: usize) -> String {
    make_error_string(
        pc,
        &format!("範囲外のメモリ番地[{ptr} (0x{ptr:x})] を参照しようとしたぞ"),
    )
}

fn read_stdin_to_u8vec() -> Vec<u8> {
    let mut line = String::new(); // 入力用のバッファ
    std::io::stdin()
        .read_line(&mut line)
        .expect("標準入力の読み込みに失敗");
    line.trim_end().as_bytes().to_owned()
}

fn println_u8(msgbuf: &mut Vec<u8>) {
    println!("{}", String::from_utf8_lossy(&msgbuf).into_owned());
    msgbuf.clear();
}

// mod BfTokens {
//     pub const INC: char = '+';
//     pub const DEC: char = '-';
//     pub const PTR_INC: char = '>';
//     pub const PTR_DEC: char = '<';
//     pub const LOOP_BEGIN: char = '[';
//     pub const LOOP_END: char = ']';
//     pub const IN: char = ',';
//     pub const OUT: char = '.';
// }

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn detect_duplicated_unique_keys() {
        assert!(Parser::new([
            "+".to_string(),
            "+-".to_string(),
            ">".to_string(),
            "<".to_string(),
            "[".to_string(),
            "]".to_string(),
            ",".to_string(),
            ".".to_string()
        ])
        .is_ok());
        assert!(Parser::new([
            "+".to_string(),
            "".to_string(),
            ">".to_string(),
            "<".to_string(),
            "[".to_string(),
            "]".to_string(),
            ",".to_string(),
            ".".to_string()
        ])
        .is_err());
        assert!(Parser::new([
            "+".to_string(),
            "+".to_string(),
            ">".to_string(),
            "<".to_string(),
            "[".to_string(),
            "]".to_string(),
            ",".to_string(),
            ".".to_string()
        ])
        .is_err());
    }

    #[test]
    fn parse() {
        let parser0 = Parser::default();
        let parser1 = Parser::new([
            "inc".to_string(),
            "_dec".to_string(),
            "あpinc".to_string(),
            "ああpdec".to_string(),
            "あ".to_string(),
            "😏lend".to_string(),
            "😏".to_string(),
            "o".to_string(),
        ])
        .unwrap();
        let program = "+あ😏lああpincあpinC";

        assert_eq!(
            Some((Token::Inc, 1usize)),
            parser0.parse_word(&program[0..program.char_indices().nth(2).unwrap().0])
        );
        assert_eq!(
            None,
            parser0.parse_word(&program[1..program.char_indices().nth(2).unwrap().0])
        );
        assert_eq!(
            Some((Token::In, 1usize)),
            parser1.parse_word(&program[program.char_indices().nth(2).unwrap().0..])
        );
        assert_eq!(
            Some((Token::LoopBegin, 1usize)),
            parser1.parse_word(&program[program.char_indices().nth(4).unwrap().0..])
        );
        assert_eq!(
            Some((Token::PtrInc, 5usize)),
            parser1.parse_word(&program[program.char_indices().nth(5).unwrap().0..])
        );
        assert_eq!(
            Some((Token::LoopBegin, 1usize)),
            parser1.parse_word(&program[program.char_indices().nth(10).unwrap().0..])
        );
    }
}
