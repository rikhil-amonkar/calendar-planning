import itertools
import json

def solve_puzzle():
    houses = [0, 1, 2, 3]  # indices for houses 1..4

    # Attribute domains
    Names = ['Peter', 'Arnold', 'Alice', 'Eric']
    Flowers = ['roses', 'daffodils', 'carnations', 'lilies']
    Hobbies = ['photography', 'painting', 'cooking', 'gardening']
    Pets = ['dog', 'fish', 'bird', 'cat']
    Colors = ['red', 'yellow', 'green', 'white']
    Styles = ['craftsman', 'colonial', 'ranch', 'victorian']

    # Helper to build rows for JSON output
    def build_rows(name, flower, hobby, pet, color, style):
        rows = []
        for i in range(4):
            rows.append([
                str(i + 1),
                name[i],
                flower[i],
                hobby[i],
                pet[i],
                color[i],
                style[i]
            ])
        return rows

    # Constraints implemented via search and pruning

    # Pre-fix HouseStyle with Craftsman in house 2 (index 1)
    # Remaining styles permuted among houses 0,2,3
    fixed_style = [None, 'craftsman', None, None]
    remaining_styles = [s for s in Styles if s != 'craftsman']

    # Pre-fix Name with Arnold in house 2 (index 1)
    fixed_name = [None, 'Arnold', None, None]
    remaining_names = [n for n in Names if n != 'Arnold']

    # Iterate over possible house styles with fixed craftsman
    for perm_styles in itertools.permutations(remaining_styles):
        style = fixed_style[:]
        style[0], style[2], style[3] = perm_styles[0], perm_styles[1], perm_styles[2]

        # Iterate over possible names with fixed Arnold
        for perm_names in itertools.permutations(remaining_names):
            name = fixed_name[:]
            name[0], name[2], name[3] = perm_names[0], perm_names[1], perm_names[2]

            # Constraint 7: Eric resides in a Victorian house
            idx_victorian = style.index('victorian')
            if name[idx_victorian] != 'Eric':
                continue

            # Colors permutations with constraints
            for perm_colors in itertools.permutations(Colors):
                color = list(perm_colors)

                # Constraint 13: Colonial == Red
                idx_colonial = style.index('colonial')
                idx_red = color.index('red')
                if idx_colonial != idx_red:
                    continue

                # Derived positional impossibilities:
                # - Red cannot be in house 1 (Peter must be left of roses/red)
                # - Red cannot be in house 4 (Cooking must be to the right of red)
                if idx_red == 0 or idx_red == 3:
                    continue

                # Constraint 12+4: Daffodils == Yellow and not in house 4
                if color[3] == 'yellow':
                    continue

                # Constraint 11 (structural): White must be to the right of Gardening -> White not at house 1
                if color[0] == 'white':
                    continue

                # Constraint 2 + 5: Roses == Red, Roses right of Peter => Peter left of Red
                idx_peter = name.index('Peter')
                if not (idx_peter < idx_red):
                    continue

                # Constraint 8+10+14: White == Fish == Carnations and Eric has Cat -> Eric cannot be White
                idx_eric = name.index('Eric')
                if color[idx_eric] == 'white':
                    continue

                # Derive flowers from colors:
                flower = [None] * 4
                # Roses at Red
                flower[idx_red] = 'roses'
                # Carnations at White
                idx_white = color.index('white')
                flower[idx_white] = 'carnations'
                # Daffodils at Yellow
                idx_yellow = color.index('yellow')
                flower[idx_yellow] = 'daffodils'
                # Remaining gets Lilies
                for i in range(4):
                    if flower[i] is None:
                        flower[i] = 'lilies'

                # Hobbies permutations with constraints 9 and 11
                for perm_hobbies in itertools.permutations(Hobbies):
                    hobby = list(perm_hobbies)

                    # Constraint 9: Cooking right of Red
                    if not (hobby.index('cooking') > idx_red):
                        continue

                    # Constraint 11: White right of Gardening
                    if not (idx_white > hobby.index('gardening')):
                        continue

                    # Pets permutations with constraints 8, 10, 14, and 3
                    for perm_pets in itertools.permutations(Pets):
                        pet = list(perm_pets)

                        # Constraint 8+10: Fish == White == Carnations
                        if pet[idx_white] != 'fish':
                            continue

                        # Constraint 14: Cat == Eric
                        if pet[idx_eric] != 'cat':
                            continue

                        # Constraint 3: Photography == Dog
                        if pet[hobby.index('photography')] != 'dog':
                            continue

                        # All constraints satisfied; return the first solution found
                        return {
                            "solution": {
                                "header": ["House", "Name", "Flower", "Hobby", "Pet", "Color", "HouseStyle"],
                                "rows": build_rows(name, flower, hobby, pet, color, style)
                            }
                        }

    raise RuntimeError("No solution found")

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))