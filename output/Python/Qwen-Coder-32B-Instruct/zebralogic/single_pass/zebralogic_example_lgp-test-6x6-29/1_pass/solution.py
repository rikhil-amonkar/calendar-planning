import itertools
import json

def solve_puzzle():
    houses = [1, 2, 3, 4, 5, 6]
    names = ['Arnold', 'Carol', 'Peter', 'Eric', 'Bob', 'Alice']
    styles = ['ranch', 'colonial', 'modern', 'craftsman', 'mediterranean', 'victorian']
    lunches = ['pizza', 'stew', 'spaghetti', 'grilled cheese', 'stir fry', 'soup']
    vacations = ['cultural', 'cruise', 'mountain', 'camping', 'city', 'beach']
    heights = ['average', 'very tall', 'very short', 'short', 'tall', 'super tall']
    cigars = ['yellow monster', 'prince', 'dunhill', 'pall mall', 'blue master', 'blends']

    # Generate all possible permutations
    all_permutations = list(itertools.permutations(range(6)))

    def is_valid(permutation):
        name_order = permutation[0]
        style_order = permutation[1]
        lunch_order = permutation[2]
        vacation_order = permutation[3]
        height_order = permutation[4]
        cigar_order = permutation[5]

        # Clue 1
        if name_order.index('Alice') != 4:
            return False
        # Clue 2
        if style_order.index('colonial') != lunch_order.index('stir fry'):
            return False
        # Clue 3
        if name_order.index('Alice') != lunch_order.index('spaghetti'):
            return False
        # Clue 4
        if name_order.index('Arnold') != lunch_order.index('stew'):
            return False
        # Clue 5
        if abs(height_order.index('average') - name_order.index('Peter')) != 1:
            return False
        # Clue 6
        if style_order[2] == 'craftsman':
            return False
        # Clue 7
        if height_order.index('average') != lunch_order.index('stir fry'):
            return False
        # Clue 8
        if style_order.index('ranch') != vacation_order.index('beach'):
            return False
        # Clue 9
        if name_order.index('Eric') != 3:
            return False
        # Clue 10
        if abs(style_order.index('colonial') - vacation_order.index('camping')) != 1:
            return False
        # Clue 11
        if vacation_order.index('mountain') != cigar_order.index('yellow monster'):
            return False
        # Clue 12
        if vacation_order.index('mountain') != height_order.index('very tall'):
            return False
        # Clue 13
        if abs(vacation_order.index('mountain') - cigar_order.index('dunhill')) != 1:
            return False
        # Clue 14
        if lunch_order.index('spaghetti') != style_order.index('victorian'):
            return False
        # Clue 15
        if height_order.index('tall') != vacation_order.index('beach'):
            return False
        # Clue 16
        if height_order.index('tall') > style_order.index('victorian'):
            return False
        # Clue 17
        if lunch_order.index('stir fry') + 1 != name_order.index('Bob'):
            return False
        # Clue 18
        if style_order.index('modern') > name_order.index('Alice'):
            return False
        # Clue 19
        if style_order.index('craftsman') > height_order.index('short'):
            return False
        # Clue 20
        if lunch_order.index('stir fry') + 1 != cigar_order.index('prince'):
            return False
        # Clue 21
        if abs(lunch_order.index('grilled cheese') - height_order.index('super tall')) != 2:
            return False
        # Clue 22
        if style_order.index('ranch') != cigar_order.index('blue master'):
            return False
        # Clue 23
        if cigar_order.index('blends') + 1 != cigar_order.index('blue master'):
            return False
        # Clue 24
        if lunch_order.index('pizza') != vacation_order.index('cultural'):
            return False
        # Clue 25
        if lunch_order.index('pizza') > vacation_order.index('cruise'):
            return False

        return True

    for permutation in itertools.product(all_permutations, repeat=6):
        if is_valid(permutation):
            name_order = permutation[0]
            style_order = permutation[1]
            lunch_order = permutation[2]
            vacation_order = permutation[3]
            height_order = permutation[4]
            cigar_order = permutation[5]

            solution = {
                "solution": {
                    "header": ["House", "Name", "Style", "Lunch", "Vacation", "Height", "Cigar"],
                    "rows": []
                }
            }

            for i in range(6):
                solution["solution"]["rows"].append([
                    str(i + 1),
                    names[name_order[i]],
                    styles[style_order[i]],
                    lunches[lunch_order[i]],
                    vacations[vacation_order[i]],
                    heights[height_order[i]],
                    cigars[cigar_order[i]]
                ])

            return json.dumps(solution, indent=2)

print(solve_puzzle())