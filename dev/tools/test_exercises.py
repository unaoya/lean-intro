"""Shared exercise numbering and immediate question/answer placement."""
import re
import unittest
from unittest.mock import patch

import lean2html as renderer
import slides


class ExerciseTest(unittest.TestCase):
    def test_global_number_does_not_change_repeated_local_solution_lookup(self):
        segments = [('prose', ['## 1. 節 {#sec-T.one}', '### ✏ 練習', '1. 最初の問い。', '2. 次の問い。']),
                    ('prose', ['### ✏ 練習', '1. 同じ節の別の練習。'])]
        solutions = [(('T.one', n), [('prose', [answer])]) for n, answer in
                     [(1, '最初の解答。'), (2, '次の解答。'), (1, '別の解答。')]]
        with patch.object(renderer, 'parse_solutions', return_value=solutions):
            body = renderer.render_chapter(renderer.CHAPTERS[0], segments, exercise_start=28)
        nodes = [n for n in slides.FragmentParser(body).root.children
                 if isinstance(n, slides.Node) and 'data-exercise' in n.attrs]
        self.assertEqual([n.tag for n in nodes], ['ol', 'details'] * 3)
        self.assertEqual([n.attrs['data-exercise'] for n in nodes], ['28', '28', '29', '29', '30', '30'])
        self.assertIn('最初の解答。', nodes[1].text)
        self.assertIn('別の解答。', nodes[5].text)
        self.assertEqual(renderer.exercise_count(segments), 3)

    def test_whole_textbook_numbering_and_each_answer_stay_together(self):
        refs = renderer.refs.analyze(renderer.SRC, renderer.CHAPTERS, renderer.SOL_FILES, renderer.parse)
        start = 1
        bodies = {}
        numbers = []
        for chapter in renderer.CHAPTERS:
            segments = renderer.parse(renderer.SRC / f'{chapter}.lean')
            body = renderer.render_chapter(chapter, segments, refs.sections, exercise_start=start)
            bodies[chapter] = body
            # Flatten notes too: supplemental exercises use the same shared sequence.
            nodes = [b.node for b in slides.blocks_from_html(body, chapter)
                     if 'data-exercise' in b.node.attrs]
            self.assertEqual(len(nodes), 2 * renderer.exercise_count(segments))
            for question, answer in zip(nodes[::2], nodes[1::2]):
                self.assertEqual((question.tag, answer.tag), ('ol', 'details'))
                self.assertEqual(question.attrs['start'], answer.attrs['data-exercise'])
                self.assertIn(f"解答 {question.attrs['start']}", answer.text)
                numbers.append(int(question.attrs['start']))
            start += renderer.exercise_count(segments)
        self.assertEqual(numbers, list(range(1, start)))
        self.assertGreater(len(numbers), 140)
        pdf = renderer.pdf_html({name: name for name in renderer.CHAPTERS}, bodies)
        self.assertEqual(len(re.findall(r'<details open class="sol"', pdf)), len(numbers))


if __name__ == '__main__':
    unittest.main()
