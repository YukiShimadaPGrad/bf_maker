mod bit_flag;
mod interpreter;

use interpreter::*;
use std::env;

enum ArgMode {
    None,
    DefOps,
    Mem,
    Exec,
    Conv,
}

fn main() {
    let mut mode = ArgMode::None;
    let mut counter = 0usize;
    let mut mem_bytes = BF_MEM_SIZE;
    let mut ops: [String; 8] = Default::default();
    let mut program_exec = String::with_capacity(0);
    let mut program_conv = String::with_capacity(0);
    if env::args().len() == 1 {
        print_help();
        return;
    }
    for arg in env::args() {
        match mode {
            ArgMode::None => {
                mode = match arg.as_str() {
                    "-h" | "--help" => {
                        print_help();
                        return;
                    }
                    "--def-ops" => ArgMode::DefOps,
                    "--memsize" => ArgMode::Mem,
                    "--exec" => ArgMode::Exec,
                    "--conv" => ArgMode::Conv,
                    _ => ArgMode::None,
                };
                continue;
            }
            ArgMode::DefOps => {
                ops[counter] = arg;
                if counter == (BF_OP_KINDS - 1) {
                    mode = ArgMode::None;
                }
            }
            ArgMode::Mem => {
                mem_bytes = arg.parse().expect("メモリサイズの指定がおかしいよ");
                mode = ArgMode::None;
            }
            ArgMode::Exec => {
                program_exec = arg;
                mode = ArgMode::None;
            }
            ArgMode::Conv => {
                program_conv = arg;
                mode = ArgMode::None;
            }
        }
        counter += 1;
    }

    let parser = match ops.iter().filter(|v| !v.is_empty()).count() {
        0 => Parser::default(),
        BF_OP_KINDS => Parser::new(ops).unwrap_or_else(|v| match v {
            ParserBuildError::HasEmptyOps => panic!("空の命令語があるぞ"),
            ParserBuildError::HasDuplicatedOps => panic!("重複した命令語があるぞ"),
        }),
        _ => panic!("命令語定義の数が足りないぞ"),
    };

    if !program_exec.is_empty() {
        if let Err(e) = interpret(&program_exec, &parser, mem_bytes) {
            eprintln!("{e}");
        }
    } else if !program_conv.is_empty() {
        println!("{}", convert(&program_conv, &parser));
    } else {
        eprintln!("実行するもの(--exec, --conv)がないよ");
    }
}

fn print_help() {
    println!(
        r#"コマンドライン
    [--def-ops '+の代わり' '-の代わり' '>の代わり' '<の代わり' '[の代わり' ']の代わり' ',の代わり' '.の代わり']
    [--memsize 正の整数]
    --execまたは--conv 実行プログラム
説明
    [--def-ops] BFの8つの命令語を任意の文字列に変更する 重複(完全一致でなければ良い)や空文字はダメだよ
    [--memsize] BF処理系のメモリサイズ[byte]を指定する 初期値は{BF_MEM_SIZE}
    --exec      後続の文字列をプログラムとして実行する --convを指定しても無視する
    --conv      後続の文字列に含まれるBFの命令語を --def-ops で指定したものに置換して出力する"#
    );
}
