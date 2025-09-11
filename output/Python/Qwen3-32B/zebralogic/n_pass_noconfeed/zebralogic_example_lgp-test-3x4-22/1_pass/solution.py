import itertools
import json

# Generate all possible permutations for names, with Peter in the first house
name_perms = []
for p in itertools.permutations(['Eric', 'Arnold']):
    name_perms.append(['Peter'] + list(p))

solution_found = None

for names in name_perms:
    for music in itertools.permutations(['pop', 'rock', 'classical']):
        for children in itertools.permutations(['Fred', 'Meredith', 'Bella']):
            for books in itertools.permutations(['mystery', 'romance', 'science fiction']):
                # Check constraint 1: Child Fred is directly left of mystery book
                idx_fred = children.index('Fred')
                if idx_fred + 1 >= 3 or books[idx_fred + 1] != 'mystery':
                    continue

                # Check constraint 5: Eric has mystery book
                i_mystery = books.index('mystery')
                if names[i_mystery] != 'Eric':
                    continue

                # Check constraint 3: mystery book has classical music
                if music[i_mystery] != 'classical':
                    continue

                # Check constraint 4: science fiction book has Meredith as child
                i_sf = books.index('science fiction')
                if children[i_sf] != 'Meredith':
                    continue

                # Check constraint 6: rock music is to the right of romance book
                i_romance_book = books.index('romance')
                i_rock = music.index('rock')
                if i_rock <= i_romance_book:
                    continue

                # All constraints satisfied, build the solution
                solution_found = {
                    "solution": {
                        "header": ["House", "Name", "MusicGenre", "Children", "BookGenre"],
                        "rows": []
                    }
                }
                for i in range(3):
                    house_num = str(i + 1)
                    solution_found["solution"]["rows"].append([
                        house_num,
                        names[i],
                        music[i],
                        children[i],
                        books[i]
                    ])
                break  # Exit inner loops
            if solution_found:
                break
        if solution_found:
            break
    if solution_found:
        break

# Output the JSON
print(json.dumps(solution_found, indent=2))