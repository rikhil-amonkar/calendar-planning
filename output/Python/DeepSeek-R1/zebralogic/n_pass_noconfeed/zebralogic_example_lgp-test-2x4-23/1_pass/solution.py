import itertools
import json

def main():
    # Define the attributes and their possible values
    names = ['Eric', 'Arnold']
    mothers = ['Aniya', 'Holly']
    car_models = ['ford f150', 'tesla model 3']
    heights = ['short', 'very short']
    
    # Generate all possible permutations for each attribute
    name_perms = list(itertools.permutations(names))
    mother_perms = list(itertools.permutations(mothers))
    car_perms = list(itertools.permutations(car_models))
    height_perms = list(itertools.permutations(heights))
    
    # Iterate through all possible combinations of attributes
    for name_assignment in name_perms:
        for mother_assignment in mother_perms:
            for car_assignment in car_perms:
                for height_assignment in height_perms:
                    # Create house assignments
                    houses = [
                        {
                            'House': '1',
                            'Name': name_assignment[0],
                            'Mother': mother_assignment[0],
                            'CarModel': car_assignment[0],
                            'Height': height_assignment[0]
                        },
                        {
                            'House': '2',
                            'Name': name_assignment[1],
                            'Mother': mother_assignment[1],
                            'CarModel': car_assignment[1],
                            'Height': height_assignment[1]
                        }
                    ]
                    
                    # Check constraints
                    # Clue 1: Tesla Model 3 is to the right of Arnold
                    arnold_house = None
                    tesla_house = None
                    for house in houses:
                        if house['Name'] == 'Arnold':
                            arnold_house = house['House']
                        if house['CarModel'] == 'tesla model 3':
                            tesla_house = house['House']
                    
                    if arnold_house is None or tesla_house is None:
                        continue
                    if not (tesla_house > arnold_house):
                        continue
                    
                    # Clue 2: Arnold is short
                    for house in houses:
                        if house['Name'] == 'Arnold' and house['Height'] != 'short':
                            break
                    else:
                        # This means Arnold was found and is short
                        pass
                    else:
                        continue
                    
                    # Clue 3: Mother Holly is in house 2
                    if houses[1]['Mother'] != 'Holly':
                        continue
                    
                    # If all constraints are satisfied, output the solution
                    solution = {
                        "solution": {
                            "header": ["House", "Name", "Mother", "CarModel", "Height"],
                            "rows": [
                                [house['House'], house['Name'], house['Mother'], house['CarModel'], house['Height']]
                                for house in houses
                            ]
                        }
                    }
                    
                    print(json.dumps(solution, indent=2))
                    return
                    
    print("No solution found")

if __name__ == "__main__":
    main()