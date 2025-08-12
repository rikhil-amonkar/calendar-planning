import itertools
import json

def solve_puzzle():
    # Define the attributes
    houses = [1, 2, 3, 4, 5]
    names = ["Alice", "Eric", "Bob", "Peter", "Arnold"]
    birthdays = ["mar", "april", "sept", "feb", "jan"]
    mothers_names = ["Holly", "Janelle", "Kailyn", "Penny", "Aniya"]
    occupations = ["engineer", "doctor", "lawyer", "artist", "teacher"]
    hair_colors = ["red", "blonde", "black", "gray", "brown"]

    # Generate all possible permutations
    permutations = list(itertools.permutations(range(5)))

    # Check each permutation against the clues
    for name_perm in permutations:
        for birthday_perm in permutations:
            for mother_perm in permutations:
                for occupation_perm in permutations:
                    for hair_color_perm in permutations:
                        # Create dictionaries for quick lookup
                        name_dict = {h: names[name_perm[i]] for i, h in enumerate(houses)}
                        birthday_dict = {h: birthdays[birthday_perm[i]] for i, h in enumerate(houses)}
                        mother_dict = {h: mothers_names[mother_perm[i]] for i, h in enumerate(houses)}
                        occupation_dict = {h: occupations[occupation_perm[i]] for i, h in enumerate(houses)}
                        hair_color_dict = {h: hair_colors[hair_color_perm[i]] for i, h in enumerate(houses)}

                        # Check each clue
                        if (birthday_dict[5] == "mar" and
                            birthday_dict[1] == "feb" and
                            occupation_dict[next(h for h, n in name_dict.items() if n == "Eric")] == "doctor" and
                            mother_dict[3] == "Janelle" and
                            occupation_dict[next(h for h, c in hair_color_dict.items() if c == "brown")] == "artist" and
                            next(h for h, o in occupation_dict.items() if o == "artist") == 4 and
                            mother_dict[next(h for h, c in hair_color_dict.items() if c == "black")] > mother_perm[hair_color_perm.index(hair_colors.index("black"))] and
                            name_dict[next(h for h, c in hair_color_dict.items() if c == "black")] == "Peter" and
                            hair_color_dict[next(h for h, o in occupation_dict.items() if o == "teacher")] == "gray" and
                            name_dict[next(h for h, m in mother_dict.items() if m == "Kailyn")] == "Alice" and
                            name_perm.index(names.index("Arnold")) > birthday_perm[birthdays.index("sept")] and
                            hair_color_dict[next(h for h, b in birthday_dict.items() if b == "jan")] == "brown" and
                            name_dict[next(h for h, c in hair_color_dict.items() if c == "blonde")] == "Arnold" and
                            mother_dict[next(h for h, c in hair_color_dict.items() if c == "black")] == "Holly" and
                            name_dict[next(h for h, o in occupation_dict.items() if o == "lawyer")] == "Peter" and
                            birthday_perm[birthdays.index("sept")] < mother_perm[mothers_names.index("Kailyn")] and
                            hair_color_dict[next(h for h, n in name_dict.items() if n == "Alice")] == "gray"):
                            
                            # Construct the solution
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Birthday", "Mother's Name", "Occupation", "Hair Color"],
                                    "rows": []
                                }
                            }
                            for house in houses:
                                solution["solution"]["rows"].append([
                                    str(house),
                                    name_dict[house],
                                    birthday_dict[house],
                                    mother_dict[house],
                                    occupation_dict[house],
                                    hair_color_dict[house]
                                ])
                            
                            return json.dumps(solution, indent=2)

# Solve the puzzle and print the result
print(solve_puzzle())