import itertools
import json

def main():
    # Define the categories
    names_list = ['Alice', 'Eric', 'Bob', 'Peter', 'Arnold']
    birthdays_list = ['mar', 'april', 'sept', 'feb', 'jan']
    mothers_list = ['Holly', 'Janelle', 'Kailyn', 'Penny', 'Aniya']
    occupations_list = ['engineer', 'doctor', 'lawyer', 'artist', 'teacher']
    hair_colors_list = ['red', 'blonde', 'black', 'gray', 'brown']

    # Generate valid birthday permutations: house 1 is feb, house 4 is jan, house 5 is mar
    valid_birthdays = []
    for p in itertools.permutations(birthdays_list):
        if p[0] == 'feb' and p[3] == 'jan' and p[4] == 'mar':
            valid_birthdays.append(p)

    # Iterate over each valid birthday permutation
    for birthdays in valid_birthdays:
        # Generate names permutations where Bob is in house 4 (index 3)
        for names in itertools.permutations(names_list):
            if names[3] != 'Bob':
                continue
            # Generate occupations based on names
            occupations = [''] * 5
            for i in range(5):
                if names[i] == 'Eric':
                    occupations[i] = 'doctor'
                elif names[i] == 'Peter':
                    occupations[i] = 'lawyer'
                elif names[i] == 'Alice':
                    occupations[i] = 'teacher'
                elif names[i] == 'Bob':
                    occupations[i] = 'artist'
                elif names[i] == 'Arnold':
                    occupations[i] = 'engineer'

            # Generate mothers permutations
            for mothers in itertools.permutations(mothers_list):
                # Generate hair color permutations that meet the conditions
                for hair_colors in itertools.permutations(hair_colors_list):
                    # Check if house 4 has brown hair
                    if hair_colors[3] != 'brown':
                        continue
                    # Check if Peter's hair is black, Arnold's is blonde, Alice's is gray, Bob's is brown
                    valid_hair = True
                    for i in range(5):
                        if names[i] == 'Peter' and hair_colors[i] != 'black':
                            valid_hair = False
                            break
                        if names[i] == 'Arnold' and hair_colors[i] != 'blonde':
                            valid_hair = False
                            break
                        if names[i] == 'Alice' and hair_colors[i] != 'gray':
                            valid_hair = False
                            break
                        if names[i] == 'Bob' and hair_colors[i] != 'brown':
                            valid_hair = False
                            break
                    if not valid_hair:
                        continue

                    # Clue 4: mother Janelle is in house 3 (index 2)
                    if mothers[2] != 'Janelle':
                        continue

                    # Clue 7: mother Penny is to the left of black hair (Peter's house)
                    peter_index = None
                    for i in range(5):
                        if names[i] == 'Peter':
                            peter_index = i
                            break
                    penny_index = None
                    for i in range(5):
                        if mothers[i] == 'Penny':
                            penny_index = i
                            break
                    if penny_index is not None and peter_index is not None:
                        if not (penny_index < peter_index):
                            continue
                    else:
                        continue

                    # Clue 10: Alice's mother is Kailyn
                    alice_index = None
                    for i in range(5):
                        if names[i] == 'Alice':
                            alice_index = i
                            break
                    if mothers[alice_index] != 'Kailyn':
                        continue

                    # Clue 11: Arnold is to the right of the person with Sept birthday
                    sept_index = None
                    for i in range(5):
                        if birthdays[i] == 'sept':
                            sept_index = i
                            break
                    arnold_index = None
                    for i in range(5):
                        if names[i] == 'Arnold':
                            arnold_index = i
                            break
                    if sept_index is not None and arnold_index is not None:
                        if not (sept_index < arnold_index):
                            continue
                    else:
                        continue

                    # Clue 14: mother Holly is the person with black hair (Peter)
                    if mothers[peter_index] != 'Holly':
                        continue

                    # Clue 16: Sept birthday is to the left of mother Kailyn (Alice's house)
                    if sept_index is not None and alice_index is not None:
                        if not (sept_index < alice_index):
                            continue
                    else:
                        continue

                    # If all constraints are met, construct the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Birthday", "Mother", "Occupation", "HairColor"],
                            "rows": []
                        }
                    }
                    for i in range(5):
                        house_num = str(i + 1)
                        name = names[i]
                        birthday = birthdays[i]
                        mother = mothers[i]
                        occupation = occupations[i]
                        hair_color = hair_colors[i]
                        solution["solution"]["rows"].append([house_num, name, birthday, mother, occupation, hair_color])
                    
                    # Output as JSON
                    print(json.dumps(solution, indent=2))
                    return  # Assuming first valid solution is the unique one

if __name__ == "__main__":
    main()