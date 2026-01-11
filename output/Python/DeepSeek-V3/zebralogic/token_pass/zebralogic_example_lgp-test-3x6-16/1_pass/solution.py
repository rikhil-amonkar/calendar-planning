import itertools
import json

def solve():
    # Define all possible values for each attribute
    names = ["Eric", "Peter", "Arnold"]
    drinks = ["tea", "water", "milk"]
    nationalities = ["dane", "brit", "swede"]
    educations = ["high school", "associate", "bachelor"]
    house_styles = ["victorian", "colonial", "ranch"]
    smoothies = ["cherry", "watermelon", "desert"]
    houses = [1, 2, 3]
    
    # Generate all permutations of each attribute across 3 houses
    all_name_perms = list(itertools.permutations(names, 3))
    all_drink_perms = list(itertools.permutations(drinks, 3))
    all_nationality_perms = list(itertools.permutations(nationalities, 3))
    all_education_perms = list(itertools.permutations(educations, 3))
    all_style_perms = list(itertools.permutations(house_styles, 3))
    all_smoothie_perms = list(itertools.permutations(smoothies, 3))
    
    solutions = []
    
    # Brute force search through all combinations
    for name_perm in all_name_perms:
        for drink_perm in all_drink_perms:
            for nationality_perm in all_nationality_perms:
                for education_perm in all_education_perms:
                    for style_perm in all_style_perms:
                        for smoothie_perm in all_smoothie_perms:
                            # Create assignment dictionaries
                            assignment = {}
                            for i in range(3):
                                house = i + 1
                                assignment[house] = {
                                    'Name': name_perm[i],
                                    'Drink': drink_perm[i],
                                    'Nationality': nationality_perm[i],
                                    'Education': education_perm[i],
                                    'HouseStyle': style_perm[i],
                                    'Smoothie': smoothie_perm[i]
                                }
                            
                            # Check all clues
                            # 1. There is one house between Eric and the tea drinker.
                            eric_house = None
                            tea_house = None
                            for house in houses:
                                if assignment[house]['Name'] == 'Eric':
                                    eric_house = house
                                if assignment[house]['Drink'] == 'tea':
                                    tea_house = house
                            if eric_house is None or tea_house is None:
                                continue
                            if abs(eric_house - tea_house) != 2:  # Exactly one house between
                                continue
                            
                            # 2. The person who likes milk is the person in a ranch-style home.
                            milk_house = None
                            ranch_house = None
                            for house in houses:
                                if assignment[house]['Drink'] == 'milk':
                                    milk_house = house
                                if assignment[house]['HouseStyle'] == 'ranch':
                                    ranch_house = house
                            if milk_house != ranch_house:
                                continue
                            
                            # 3. The person with a bachelor's degree is in the second house.
                            if assignment[2]['Education'] != 'bachelor':
                                continue
                            
                            # 4. The person with a high school diploma is the Dane.
                            for house in houses:
                                if assignment[house]['Education'] == 'high school' and assignment[house]['Nationality'] != 'dane':
                                    break
                                if assignment[house]['Nationality'] == 'dane' and assignment[house]['Education'] != 'high school':
                                    break
                            else:
                                # Check that exactly one person is Dane with high school
                                dane_high_school_count = 0
                                for house in houses:
                                    if assignment[house]['Nationality'] == 'dane' and assignment[house]['Education'] == 'high school':
                                        dane_high_school_count += 1
                                if dane_high_school_count != 1:
                                    continue
                            # Additional check to ensure the constraint is properly satisfied
                            dane_house = None
                            high_school_house = None
                            for house in houses:
                                if assignment[house]['Nationality'] == 'dane':
                                    dane_house = house
                                if assignment[house]['Education'] == 'high school':
                                    high_school_house = house
                            if dane_house != high_school_house:
                                continue
                            
                            # 5. The Desert smoothie lover is the Swedish person.
                            for house in houses:
                                if assignment[house]['Smoothie'] == 'desert' and assignment[house]['Nationality'] != 'swede':
                                    break
                                if assignment[house]['Nationality'] == 'swede' and assignment[house]['Smoothie'] != 'desert':
                                    break
                            else:
                                # Check that exactly one person is Swede with desert smoothie
                                swede_desert_count = 0
                                for house in houses:
                                    if assignment[house]['Nationality'] == 'swede' and assignment[house]['Smoothie'] == 'desert':
                                        swede_desert_count += 1
                                if swede_desert_count != 1:
                                    continue
                            # Additional check
                            swede_house = None
                            desert_house = None
                            for house in houses:
                                if assignment[house]['Nationality'] == 'swede':
                                    swede_house = house
                                if assignment[house]['Smoothie'] == 'desert':
                                    desert_house = house
                            if swede_house != desert_house:
                                continue
                            
                            # 6. The person residing in a Victorian house is not in the first house.
                            if assignment[1]['HouseStyle'] == 'victorian':
                                continue
                            
                            # 7. The person who likes Cherry smoothies is the person living in a colonial-style house.
                            for house in houses:
                                if assignment[house]['Smoothie'] == 'cherry' and assignment[house]['HouseStyle'] != 'colonial':
                                    break
                                if assignment[house]['HouseStyle'] == 'colonial' and assignment[house]['Smoothie'] != 'cherry':
                                    break
                            else:
                                # Check that exactly one person has cherry smoothie and colonial style
                                cherry_colonial_count = 0
                                for house in houses:
                                    if assignment[house]['Smoothie'] == 'cherry' and assignment[house]['HouseStyle'] == 'colonial':
                                        cherry_colonial_count += 1
                                if cherry_colonial_count != 1:
                                    continue
                            # Additional check
                            cherry_house = None
                            colonial_house = None
                            for house in houses:
                                if assignment[house]['Smoothie'] == 'cherry':
                                    cherry_house = house
                                if assignment[house]['HouseStyle'] == 'colonial':
                                    colonial_house = house
                            if cherry_house != colonial_house:
                                continue
                            
                            # 8. Arnold is somewhere to the right of the person residing in a Victorian house.
                            arnold_house = None
                            victorian_house = None
                            for house in houses:
                                if assignment[house]['Name'] == 'Arnold':
                                    arnold_house = house
                                if assignment[house]['HouseStyle'] == 'victorian':
                                    victorian_house = house
                            if arnold_house is None or victorian_house is None:
                                continue
                            if arnold_house <= victorian_house:
                                continue
                            
                            # 9. The person in a ranch-style home is the person with a high school diploma.
                            for house in houses:
                                if assignment[house]['HouseStyle'] == 'ranch' and assignment[house]['Education'] != 'high school':
                                    break
                                if assignment[house]['Education'] == 'high school' and assignment[house]['HouseStyle'] != 'ranch':
                                    break
                            else:
                                # Check that exactly one person has ranch style and high school
                                ranch_high_school_count = 0
                                for house in houses:
                                    if assignment[house]['HouseStyle'] == 'ranch' and assignment[house]['Education'] == 'high school':
                                        ranch_high_school_count += 1
                                if ranch_high_school_count != 1:
                                    continue
                            # Additional check
                            ranch_house = None
                            high_school_house = None
                            for house in houses:
                                if assignment[house]['HouseStyle'] == 'ranch':
                                    ranch_house = house
                                if assignment[house]['Education'] == 'high school':
                                    high_school_house = house
                            if ranch_house != high_school_house:
                                continue
                            
                            # All constraints satisfied
                            solutions.append(assignment)
    
    # Convert solution to required format
    if solutions:
        # Take the first solution (should be only one)
        solution = solutions[0]
        rows = []
        for house in sorted(solution.keys()):
            row = [str(house)]
            row.append(solution[house]['Name'])
            row.append(solution[house]['Drink'])
            row.append(solution[house]['Nationality'])
            row.append(solution[house]['Education'])
            row.append(solution[house]['HouseStyle'])
            row.append(solution[house]['Smoothie'])
            rows.append(row)
        
        result = {
            "solution": {
                "header": ["House", "Name", "Drink", "Nationality", "Education", "HouseStyle", "Smoothie"],
                "rows": rows
            }
        }
        return json.dumps(result, indent=2)
    else:
        return json.dumps({"error": "No solution found"}, indent=2)

if __name__ == "__main__":
    print(solve())