# Equivalência entre o Princípio da Indução Matemática (PIM) e o Princípio da Indução Forte (PIF)

Este repositório contém o projeto desenvolvido para a disciplina **Lógica Computacional 1 (LC1)**, do Departamento de Ciência da Computação da Universidade de Brasília (UnB).  
O objetivo é demonstrar formalmente, utilizando o assistente de provas **Rocq/Coq**, que o **Princípio de Indução Matemática (PIM)** e o **Princípio de Indução Forte (PIF)** são logicamente equivalentes.

---

## Estrutura do Repositório
``` bash
├── ind_equiv.v # Código em Rocq/Coq contendo as provas formais
└── relatorio.pdf # Relatório com explicações e desenvolvimento do projeto
```

## Sobre o Projeto

O trabalho aborda:

- As definições formais dos princípios de indução.
- A prova de que **PIF implica PIM** (Lema 1).
- A prova de que **PIM implica PIF** (Lema 2).
- A demonstração final da equivalência: PIM ↔ PIF

Esse resultado mostra que ambos os princípios possuem o mesmo poder dedutivo: qualquer prova construída com um deles pode ser reestruturada usando o outro, dependendo da conveniência.

---

## Como Executar o Código

Você pode abrir o arquivo `ind_equiv.v` de duas formas:

### **1. Ambiente local**

1. Instale **Coq** ou **Rocq**.
2. Abra o arquivo usando:
   - **CoqIDE**, ou  
   - **VS Code** com a extensão **VSCoq**.
3. Carregue o arquivo e navegue pela prova passo a passo.

### **2. Via jsCoq (versão web)**

O jsCoq pode ser utilizado diretamente pelo navegador, no entanto apresenta **instabilidades conhecidas**, o que pode afetar a execução do arquivo.  
Caso encontre problemas, opte pela execução local.

---

## Autores

- Ana Luísa de Souza Paraguassu - 231003442
- Arthur Menezes Botelho - 231003362
- Pedro Lucas Pereira Neris - 231018964
