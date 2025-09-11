import itertools
import json

def solve_puzzle():
    # Define the possible values for each category
    names = ["Arnold", "Eric"]
    occupations = ["engineer", "doctor"]
    birthdays = ["april", "sept"]
    house_styles = ["victorian", "colonial"]
    heights = ["very short", "short"]
    cigars = ["pall mall", "prince"]

    # Generate all possible permutations for the two houses
    all_permutations = list(itertools.product(names, occupations, birthdays, house_styles, heights, cigars))

    # Function to check if a given permutation satisfies all the clues
    def is_valid(house1, house2):
        # Unpack the tuples
        name1, occ1, bday1, style1, height1, cigar1 = house1
        name2, occ2, bday2, style2, height2, cigar2 = house2

        # Check clue 1: The person who is an engineer is in the first house.
        if occ1 != "engineer":
            return False

        # Check clue 2: The person whose birthday is in April and the person who is a doctor are next to each other.
        if (bday1 == "april" and occ2 != "doctor") and (bday2 == "april" and occ1 != "doctor"):
            return False

        # Check clue 3: The person living in a colonial-style house is the person who is an engineer.
        if style1 != "colonial" and occ1 == "engineer":
            return False

        # Check clue 4: The person who is very short is the person who is an engineer.
        if height1 != "very short" and occ1 == "engineer":
            return False

        # Check clue 5: The person who is short is the person partial to Pall Mall.
        if height2 != "short" or cigar2 != "pall mall":
            return False

        # Check clue 6: The person who is an engineer is Eric.
        if name1 != "Eric" and occ1 == "engineer":
            return False

        # Ensure all names, occupations, birthdays, house styles, heights, and cigars are unique
        if len(set([name1, name2])) != 2:
            return False
        if len(set([occ1, occ2])) != 2:
            return False
        if len(set([bday1, bday2])) != 2:
            return False
        if len(set([style1, style2])) != 2:
            return False
        if len(set([height1, height2])) != 2:
            return False
        if len(set([cigar1, cigar2])) != 2:
            return False

        return True

    # Iterate over all permutations to find the valid solution
    for house1 in all_permutations:
        for house2 in all_permutations:
            if is_valid(house1, house2):
                solution = {
                    "solution": {
                        "header": ["House", "Name", "Occupation", "Birthday", "HouseStyle", "Height", "Cigar"],
                        "rows": [
                            ["1", house1[0], house1[1], house1[2], house1[3], house1[4], house1[5]],
                            ["2", house2[0], house2[1], house2[2], house2[3], house2[4], house2[5]]
                        ]
                    }
                }
                return json.dumps(solution, indent=2)

# Run the function and print the result
print(solve_puzzle())