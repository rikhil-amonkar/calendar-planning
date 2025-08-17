import itertools
import json

# Define all possible values
names_list = ['Alice', 'Peter', 'Bob', 'Eric', 'Arnold']
heights_list = ['average', 'short', 'tall', 'very short', 'very tall']
mothers_list = ['Janelle', 'Kailyn', 'Penny', 'Holly', 'Aniya']
hair_colors_list = ['blonde', 'black', 'gray', 'red', 'brown']

# Generate valid height permutations: house 1 (index 0) is 'average', house 4 (index 3) is 'short'
remaining_heights = ['tall', 'very short', 'very tall']
valid_heights = []
for h2, h3, h5 in itertools.permutations(remaining_heights):
    heights = ['average', h2, h3, 'short', h5]
    valid_heights.append(heights)

# Generate valid mother permutations: house 3 (index 2) is 'Kailyn'
remaining_mothers = ['Janelle', 'Penny', 'Holly', 'Aniya']
valid_mothers = []
for m in itertools.permutations(remaining_mothers):
    mothers = [m[0], m[1], 'Kailyn', m[2], m[3]]
    valid_mothers.append(mothers)

solution_found = None

for heights in valid_heights:
    for mothers in valid_mothers:
        # Generate all possible name permutations
        for names in itertools.permutations(names_list):
            # Check constraint 8: Bob is in house 5 (index 4)
            if names[4] != 'Bob':
                continue
            # Generate all possible hair color permutations
            for hair_colors in itertools.permutations(hair_colors_list):
                # Check constraint 5: Eric has black hair
                try:
                    eric_index = names.index('Eric')
                except ValueError:
                    continue  # Should not happen with permutations
                if hair_colors[eric_index] != 'black':
                    continue
                # Check constraint 4: black not in house 4 (index 3)
                if hair_colors[3] == 'black':
                    continue
                # Check constraint 9: Peter has red hair
                try:
                    peter_index = names.index('Peter')
                except ValueError:
                    continue
                if hair_colors[peter_index] != 'red':
                    continue
                # Check constraint 11: Arnold has brown hair
                try:
                    arnold_index = names.index('Arnold')
                except ValueError:
                    continue
                if hair_colors[arnold_index] != 'brown':
                    continue
                # Check constraint 1: tall's mother is Holly
                valid = True
                for i in range(5):
                    if heights[i] == 'tall' and mothers[i] != 'Holly':
                        valid = False
                        break
                if not valid:
                    continue
                # Check constraint 6: very short's mother is Penny
                for i in range(5):
                    if heights[i] == 'very short' and mothers[i] != 'Penny':
                        valid = False
                        break
                if not valid:
                    continue
                # Check constraint 7: Eric and gray are adjacent
                try:
                    gray_index = hair_colors.index('gray')
                except ValueError:
                    continue
                if abs(eric_index - gray_index) != 1:
                    continue
                # Check constraint 3: gray is directly left of Janelle's mother
                try:
                    janelle_mother_index = mothers.index('Janelle')
                except ValueError:
                    continue
                if (gray_index + 1) != janelle_mother_index:
                    continue
                # Check constraint 12: brown is left of Janelle's mother
                try:
                    brown_index = hair_colors.index('brown')
                except ValueError:
                    continue
                if brown_index >= janelle_mother_index:
                    continue
                # Check constraint 13: Aniya and very short are adjacent
                try:
                    aniya_mother_index = mothers.index('Aniya')
                except ValueError:
                    continue
                try:
                    very_short_index = heights.index('very short')
                except ValueError:
                    continue
                if abs(aniya_mother_index - very_short_index) != 1:
                    continue

                # If all constraints are satisfied
                solution_found = {
                    "solution": {
                        "header": ["House", "Name", "Height", "Mother", "HairColor"],
                        "rows": []
                    }
                }
                for i in range(5):
                    house_num = str(i + 1)
                    name = names[i]
                    height = heights[i]
                    mother = mothers[i]
                    hair_color = hair_colors[i]
                    solution_found["solution"]["rows"].append([house_num, name, height, mother, hair_color])
                # Found solution, break out
                break
            if solution_found:
                break
        if solution_found:
            break
    if solution_found:
        break

# Output the JSON
print(json.dumps(solution_found, indent=2))