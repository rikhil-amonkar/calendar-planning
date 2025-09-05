import itertools
import json

def main():
    names_list = ["Arnold", "Eric", "Peter"]
    cigars_list = ["pall mall", "blue master", "prince"]
    animals_list = ["horse", "cat", "bird"]
    children_list = ["Bella", "Fred", "Meredith"]
    book_list = ["science fiction", "romance", "mystery"]
    phones_list = ["google pixel 6", "iphone 13", "samsung galaxy s21"]

    # Iterate over all possible assignments using permutations
    for names in itertools.permutations(names_list):
        # Clue 8: Peter is somewhere to the left of Eric.
        if names.index("Peter") >= names.index("Eric"):
            continue

        for cigars in itertools.permutations(cigars_list):
            # Clue 3: The person partial to Pall Mall is in the second house.
            if cigars[1] != "pall mall":
                continue

            for animals in itertools.permutations(animals_list):
                # Clue 2: The cat lover is Eric.
                # Ensure that the house with Eric has the cat.
                if animals[names.index("Eric")] != "cat":
                    continue

                for children in itertools.permutations(children_list):
                    for books in itertools.permutations(book_list):
                        # Clue 10: The person who loves science fiction is in the third house.
                        if books[2] != "science fiction":
                            continue
                        # Clue 11: The person who loves mystery books is not in the second house.
                        if books[1] == "mystery":
                            continue

                        for phones in itertools.permutations(phones_list):
                            # Clue 6 (with deduction):
                            # The person who uses an iPhone 13 must be directly left of the person who uses a Samsung Galaxy S21.
                            # Since the science fiction fan in house 3 must have a Samsung Galaxy S21 (clue 9), 
                            # house2 must be iPhone 13.
                            if phones[1] != "iphone 13" or phones[2] != "samsung galaxy s21":
                                continue

                            # Build the candidate houses.
                            houses = []
                            for i in range(3):
                                house = {
                                    "House": str(i+1),
                                    "Name": names[i],
                                    "Cigar": cigars[i],
                                    "Animal": animals[i],
                                    "Children": children[i],
                                    "BookGenre": books[i],
                                    "PhoneModel": phones[i]
                                }
                                houses.append(house)

                            # Check house-specific (bidirectional) constraints.
                            valid = True
                            for house in houses:
                                # Clue 1: The person who loves mystery books has a child named Fred.
                                if (house["BookGenre"] == "mystery") != (house["Children"] == "Fred"):
                                    valid = False
                                    break
                                # Clue 4: The person who keeps horses has a child named Meredith.
                                if (house["Animal"] == "horse") != (house["Children"] == "Meredith"):
                                    valid = False
                                    break
                                # Clue 5: The person whose child is named Bella is the Prince smoker.
                                if (house["Children"] == "Bella") != (house["Cigar"] == "prince"):
                                    valid = False
                                    break
                                # Clue 2 (symmetry): The cat lover must be Eric.
                                if (house["Name"] == "Eric") != (house["Animal"] == "cat"):
                                    valid = False
                                    break
                                # Clue 9: The person who loves science fiction uses a Samsung Galaxy S21.
                                if (house["BookGenre"] == "science fiction") != (house["PhoneModel"] == "samsung galaxy s21"):
                                    valid = False
                                    break
                            if not valid:
                                continue

                            # Clue 7: The person whose child is Fred is directly left of Arnold.
                            fred_left_of_arnold = False
                            for i in range(2):
                                if houses[i]["Children"] == "Fred" and houses[i+1]["Name"] == "Arnold":
                                    fred_left_of_arnold = True
                                    break
                            if not fred_left_of_arnold:
                                continue

                            # Clue 6 (check adjacency on phones in case there is any alternative):
                            iphone_left_of_samsung = False
                            for i in range(2):
                                if houses[i]["PhoneModel"] == "iphone 13" and houses[i+1]["PhoneModel"] == "samsung galaxy s21":
                                    iphone_left_of_samsung = True
                                    break
                            if not iphone_left_of_samsung:
                                continue

                            # All constraints are satisfied; output the solution.
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Cigar", "Animal", "Children", "BookGenre", "PhoneModel"],
                                    "rows": []
                                }
                            }
                            for house in houses:
                                row = [
                                    house["House"],
                                    house["Name"],
                                    house["Cigar"],
                                    house["Animal"],
                                    house["Children"],
                                    house["BookGenre"],
                                    house["PhoneModel"]
                                ]
                                solution["solution"]["rows"].append(row)
                            
                            print(json.dumps(solution, indent=2))
                            return

if __name__ == "__main__":
    main()