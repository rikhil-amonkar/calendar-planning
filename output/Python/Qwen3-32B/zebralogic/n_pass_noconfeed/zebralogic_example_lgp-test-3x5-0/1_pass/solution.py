import itertools
import json

for names in itertools.permutations(['Eric', 'Arnold', 'Peter']):
    if names[0] != 'Eric':
        continue
    for books in itertools.permutations(['science fiction', 'mystery', 'romance']):
        for smoothies in itertools.permutations(['watermelon', 'desert', 'cherry']):
            if smoothies[0] != 'watermelon':
                continue
            if smoothies[1] == 'cherry':
                continue
            for birthdays in itertools.permutations(['april', 'jan', 'sept']):
                if birthdays[0] == 'jan':
                    continue
                for heights in itertools.permutations(['average', 'very short', 'short']):
                    # Check Arnold's book is mystery
                    arnold_index = names.index('Arnold')
                    if books[arnold_index] != 'mystery':
                        continue
                    # Check very short has romance book
                    very_short_pos = heights.index('very short')
                    if books[very_short_pos] != 'romance':
                        continue
                    # Check mystery's birthday is sept
                    mystery_pos = books.index('mystery')
                    if birthdays[mystery_pos] != 'sept':
                        continue
                    # Check average height has desert smoothie
                    average_pos = heights.index('average')
                    if smoothies[average_pos] != 'desert':
                        continue
                    # Check short has watermelon
                    short_pos = heights.index('short')
                    if smoothies[short_pos] != 'watermelon':
                        continue
                    
                    # All constraints satisfied
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "BookGenre", "Smoothie", "Birthday", "Height"],
                            "rows": []
                        }
                    }
                    for i in range(3):
                        house = str(i+1)
                        solution["solution"]["rows"].append([
                            house,
                            names[i],
                            books[i],
                            smoothies[i],
                            birthdays[i],
                            heights[i]
                        ])
                    print(json.dumps(solution))
                    exit()