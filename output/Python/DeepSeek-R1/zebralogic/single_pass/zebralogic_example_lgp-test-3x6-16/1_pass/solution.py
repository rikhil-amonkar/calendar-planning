import itertools
import json

def main():
    # Define the attribute domains
    names = ['Eric', 'Peter', 'Arnold']
    drinks = ['tea', 'water', 'milk']
    nationalities = ['dane', 'brit', 'swede']
    educations = ['high school', 'associate', 'bachelor']
    house_styles = ['victorian', 'colonial', 'ranch']
    smoothies = ['cherry', 'watermelon', 'desert']
    
    # Generate all permutations for each attribute
    for n_perm in itertools.permutations(names):
        for d_perm in itertools.permutations(drinks):
            for nat_perm in itertools.permutations(nationalities):
                for edu_perm in itertools.permutations(educations):
                    # Check clue3: bachelor is in second house (index 1)
                    if edu_perm[1] != 'bachelor':
                        continue
                    for hs_perm in itertools.permutations(house_styles):
                        # Check clue6: victorian not in first house (index 0)
                        if hs_perm[0] == 'victorian':
                            continue
                        for sm_perm in itertools.permutations(smoothies):
                            # Check clue1: one house between Eric and tea drinker
                            try:
                                eric_idx = n_perm.index('Eric')
                                tea_idx = d_perm.index('tea')
                            except ValueError:
                                continue
                            if abs(eric_idx - tea_idx) != 2:
                                continue
                            
                            # Check clue2: milk drinker is in ranch-style home
                            try:
                                milk_idx = d_perm.index('milk')
                                ranch_idx = hs_perm.index('ranch')
                            except ValueError:
                                continue
                            if milk_idx != ranch_idx:
                                continue
                            
                            # Check clue4: high school diploma is the Dane
                            try:
                                hs_edu_idx = edu_perm.index('high school')
                            except ValueError:
                                continue
                            if nat_perm[hs_edu_idx] != 'dane':
                                continue
                            
                            # Check clue5: desert smoothie lover is Swede
                            try:
                                desert_idx = sm_perm.index('desert')
                            except ValueError:
                                continue
                            if nat_perm[desert_idx] != 'swede':
                                continue
                            
                            # Check clue7: cherry smoothie is in colonial house
                            try:
                                cherry_idx = sm_perm.index('cherry')
                                colonial_idx = hs_perm.index('colonial')
                            except ValueError:
                                continue
                            if cherry_idx != colonial_idx:
                                continue
                            
                            # Check clue8: Arnold is to the right of Victorian house
                            try:
                                victorian_idx = hs_perm.index('victorian')
                                arnold_idx = n_perm.index('Arnold')
                            except ValueError:
                                continue
                            if arnold_idx <= victorian_idx:
                                continue
                            
                            # Check clue9: ranch-style home has high school diploma
                            try:
                                ranch_idx = hs_perm.index('ranch')
                            except ValueError:
                                continue
                            if edu_perm[ranch_idx] != 'high school':
                                continue
                            
                            # If all constraints pass, format the solution
                            solution = {
                                "solution": {
                                    "header": ["House", "Name", "Drink", "Nationality", "Education", "House Style", "Smoothie"],
                                    "rows": [
                                        ["1", n_perm[0], d_perm[0], nat_perm[0], edu_perm[0], hs_perm[0], sm_perm[0]],
                                        ["2", n_perm[1], d_perm[1], nat_perm[1], edu_perm[1], hs_perm[1], sm_perm[1]],
                                        ["3", n_perm[2], d_perm[2], nat_perm[2], edu_perm[2], hs_perm[2], sm_perm[2]]
                                    ]
                                }
                            }
                            print(json.dumps(solution, indent=2))
                            return
    print(json.dumps({}))  # No solution found

if __name__ == "__main__":
    main()