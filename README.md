# Name

BF_maker

## Overview

たった8つの記号 ` + - > < [ ] , . ` だけで書ける、[名状し難いあの難読プログラミング言語](https://ja.wikibooks.org/wiki/Brainfuck) のRust実装  
命令語を好きな文字列(utf8対応)に置き換えたり、既存のプログラムを変換できたりする

## Usage

- 通常のプログラムを実行する
  ```sh
  bf_maker --exec "++++++++++[->++++++++++>+++>++++++++++++>+++++>+++++++<<<<<]>>>>>++.<<<<+.+++++++..+++.>++.>-.<<.+++.------.--------.>>>----."
  # output: ぬ
  ```
- 通常のプログラムを任意の命令語セットに変換する
  ```sh
  bf_maker --def-ops "ぷに" "もち" "ぽよ" "もみ" "かり" "さく" "かち" "こち" \
           --conv "+++++[->+++++<]>[->+++++++++>+++++>+++++++<<<]>++.>++++.>---."
  # output: ぷにぷにぷにぷにぷにかりもちぽよぷにぷにぷにぷにぷにもみさくぽよかりもちぽよぷにぷにぷにぷにぷにぷにぷにぷにぷにぽよぷにぷにぷにぷにぷにぽよぷにぷにぷにぷにぷにぷにぷにもみもみもみさくぽよぷにぷにこちぽよぷにぷにぷにぷにこちぽよもちもちもちこち
  ```

- 任意の命令語セットのプログラムを実行する
  ```sh
  bf_maker --def-ops "ぷに" "もち" "ぽよ" "もみ" "かり" "さく" "かち" "こち" \
           --exec "ぷにぷにぷにぷにぷにかりもちぽよぷにぷにぷにぷにぷにもみさくぽよかりもちぽよぷにぷにぷにぷにぷにぷにぷにぷにぷにぽよぷにぷにぷにぷにぷにぽよぷにぷにぷにぷにぷにぷにぷにもみもみもみさくぽよぷにぷにこちぽよぷにぷにぷにぷにこちぽよもちもちもちこち"
  # output: ぬ
  ```

## Features

- [名状し難いあの難読プログラミング言語](https://ja.wikibooks.org/wiki/Brainfuck)のインタプリタ
  - utf8文字列入出力ができる
- 命令語の自由な置き換え
- 通常版プログラムから、命令語を置き換えたプログラムへの変換

## Author

Yuki Shimada

## Licence

[MIT](https://opensource.org/licenses/mit-license.php)