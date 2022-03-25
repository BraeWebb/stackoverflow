from parser import ParserError
from unittest import assert_raises
import parser

def peek(word_list):
    if word_list:
        word = word_list[0]
        return word[0]
    else:
        return None

def match(word_list, expecting):
    if word_list:
        word = word_list.pop(0)

        if word[0] == expecting:
            return word
        else:
            return None
    else:
        return None

def skip(word_list, word_type):
    while peek(word_list) == word_type:
        match(word_list, word_type)


def parse_verb(word_list):
    skip(word_list, 'stop')
    next_word = peek(word_list)

    if next_word == 'verb':
        return match(word_list, 'verb')
    else:
        return ParserError("Expected a verb next.")


def test_verb():
    assert_raises(parser.ParserError, parser.parse_verb, [('noun', 'princess'),
                                                          ('verb', 'open'),
                                                          ('stop', 'the'),
                                                          ('noun', 'door')])