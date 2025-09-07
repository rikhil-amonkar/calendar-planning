import json
from itertools import permutations

def main():
    # Define all possible values for each category
    names = ['Arnold', 'Carol', 'Eric', 'Bob', 'Alice', 'Peter']
    birthdays = ['feb', 'mar', 'sept', 'jan', 'may', 'april']
    foods = ['stew', 'soup', 'grilled cheese', 'stir fry', 'spaghetti', 'pizza']
    heights = ['very short', 'average', 'super tall', 'short', 'very tall', 'tall']
    car_models = ['chevrolet silverado', 'ford f150', 'bmw 3 series', 'tesla model 3', 'toyota camry', 'honda civic']
    
    houses = [1, 2, 3, 4, 5, 6]
    
    # Generate all possible permutations for each category
    for name_perm in permutations(names):
        for bday_perm in permutations(birthdays):
            for food_perm in permutations(foods):
                for height_perm in permutations(heights):
                    for car_perm in permutations(car_models):
                        # Create assignment dictionaries for each house
                        assignment = {}
                        for i, house in enumerate(houses):
                            assignment[house] = {
                                'name': name_perm[i],
                                'birthday': bday_perm[i],
                                'food': food_perm[i],
                                'height': height_perm[i],
                                'car': car_perm[i]
                            }
                        
                        # Check all constraints
                        # Clue 1: The person who owns a Honda Civic is the person who is short.
                        honda_civic_owner = None
                        short_person = None
                        for house, attrs in assignment.items():
                            if attrs['car'] == 'honda civic':
                                honda_civic_owner = house
                            if attrs['height'] == 'short':
                                short_person = house
                        if honda_civic_owner != short_person:
                            continue
                        
                        # Clue 2: The person who owns a Ford F-150 is in the fifth house.
                        if assignment[5]['car'] != 'ford f150':
                            continue
                        
                        # Clue 3: The person who loves stir fry is somewhere to the left of Eric.
                        stir_fry_house = None
                        eric_house = None
                        for house, attrs in assignment.items():
                            if attrs['food'] == 'stir fry':
                                stir_fry_house = house
                            if attrs['name'] == 'Eric':
                                eric_house = house
                        if stir_fry_house is None or eric_house is None or stir_fry_house >= eric_house:
                            continue
                        
                        # Clue 4: The person whose birthday is in May is somewhere to the left of Carol.
                        may_bday_house = None
                        carol_house = None
                        for house, attrs in assignment.items():
                            if attrs['birthday'] == 'may':
                                may_bday_house = house
                            if attrs['name'] == 'Carol':
                                carol_house = house
                        if may_bday_house is None or carol_house is None or may_bday_house >= carol_house:
                            continue
                        
                        # Clue 5: The person who is very short is somewhere to the left of the person whose birthday is in April.
                        very_short_house = None
                        april_bday_house = None
                        for house, attrs in assignment.items():
                            if attrs['height'] == 'very short':
                                very_short_house = house
                            if attrs['birthday'] == 'april':
                                april_bday_house = house
                        if very_short_house is None or april_bday_house is None or very_short_house >= april_bday_house:
                            continue
                        
                        # Clue 6: The person who owns a BMW 3 Series is not in the third house.
                        if assignment[3]['car'] == 'bmw 3 series':
                            continue
                        
                        # Clue 7: There are two houses between the person who loves stir fry and the person who is a pizza lover.
                        stir_fry_house = None
                        pizza_house = None
                        for house, attrs in assignment.items():
                            if attrs['food'] == 'stir fry':
                                stir_fry_house = house
                            if attrs['food'] == 'pizza':
                                pizza_house = house
                        if stir_fry_house is None or pizza_house is None or abs(stir_fry_house - pizza_house) != 3:
                            continue
                        
                        # Clue 8: The person who loves the soup is directly left of Eric.
                        soup_house = None
                        eric_house = None
                        for house, attrs in assignment.items():
                            if attrs['food'] == 'soup':
                                soup_house = house
                            if attrs['name'] == 'Eric':
                                eric_house = house
                        if soup_house is None or eric_house is None or soup_house != eric_house - 1:
                            continue
                        
                        # Clue 9: The person who loves the spaghetti eater and the person whose birthday is in May are next to each other.
                        spaghetti_house = None
                        may_bday_house = None
                        for house, attrs in assignment.items():
                            if attrs['food'] == 'spaghetti':
                                spaghetti_house = house
                            if attrs['birthday'] == 'may':
                                may_bday_house = house
                        if spaghetti_house is None or may_bday_house is None or abs(spaghetti_house - may_bday_house) != 1:
                            continue
                        
                        # Clue 10: Alice is directly left of the person who owns a BMW 3 Series.
                        alice_house = None
                        bmw_house = None
                        for house, attrs in assignment.items():
                            if attrs['name'] == 'Alice':
                                alice_house = house
                            if attrs['car'] == 'bmw 3 series':
                                bmw_house = house
                        if alice_house is None or bmw_house is None or alice_house != bmw_house - 1:
                            continue
                        
                        # Clue 11: The person who owns a Tesla Model 3 is somewhere to the left of the person who is tall.
                        tesla_house = None
                        tall_house = None
                        for house, attrs in assignment.items():
                            if attrs['car'] == 'tesla model 3':
                                tesla_house = house
                            if attrs['height'] == 'tall':
                                tall_house = house
                        if tesla_house is None or tall_house is None or tesla_house >= tall_house:
                            continue
                        
                        # Clue 12: The person who is very tall is the person who owns a Toyota Camry.
                        very_tall_house = None
                        toyota_house = None
                        for house, attrs in assignment.items():
                            if attrs['height'] == 'very tall':
                                very_tall_house = house
                            if attrs['car'] == 'toyota camry':
                                toyota_house = house
                        if very_tall_house != toyota_house:
                            continue
                        
                        # Clue 13: Peter is directly left of the person who is a pizza lover.
                        peter_house = None
                        pizza_house = None
                        for house, attrs in assignment.items():
                            if attrs['name'] == 'Peter':
                                peter_house = house
                            if attrs['food'] == 'pizza':
                                pizza_house = house
                        if peter_house is None or pizza_house is None or peter_house != pizza_house - 1:
                            continue
                        
                        # Clue 14: The person who loves the stew is not in the third house.
                        if assignment[3]['food'] == 'stew':
                            continue
                        
                        # Clue 15: There is one house between the person whose birthday is in September and the person who is very short.
                        sept_bday_house = None
                        very_short_house = None
                        for house, attrs in assignment.items():
                            if attrs['birthday'] == 'sept':
                                sept_bday_house = house
                            if attrs['height'] == 'very short':
                                very_short_house = house
                        if sept_bday_house is None or very_short_house is None or abs(sept_bday_house - very_short_house) != 2:
                            continue
                        
                        # Clue 16: There is one house between the person whose birthday is in March and the person who is super tall.
                        mar_bday_house = None
                        super_tall_house = None
                        for house, attrs in assignment.items():
                            if attrs['birthday'] == 'mar':
                                mar_bday_house = house
                            if attrs['height'] == 'super tall':
                                super_tall_house = house
                        if mar_bday_house is None or super_tall_house is None or abs(mar_bday_house - super_tall_house) != 2:
                            continue
                        
                        # Clue 17: The person who is tall is Bob.
                        tall_house = None
                        bob_house = None
                        for house, attrs in assignment.items():
                            if attrs['height'] == 'tall':
                                tall_house = house
                            if attrs['name'] == 'Bob':
                                bob_house = house
                        if tall_house != bob_house:
                            continue
                        
                        # Clue 18: The person whose birthday is in May is somewhere to the right of Alice.
                        may_bday_house = None
                        alice_house = None
                        for house, attrs in assignment.items():
                            if attrs['birthday'] == 'may':
                                may_bday_house = house
                            if attrs['name'] == 'Alice':
                                alice_house = house
                        if may_bday_house is None or alice_house is None or may_bday_house <= alice_house:
                            continue
                        
                        # Clue 19: The person who is very short is in the fourth house.
                        if assignment[4]['height'] != 'very short':
                            continue
                        
                        # Clue 20: The person whose birthday is in March is the person who is short.
                        mar_bday_house = None
                        short_house = None
                        for house, attrs in assignment.items():
                            if attrs['birthday'] == 'mar':
                                mar_bday_house = house
                            if attrs['height'] == 'short':
                                short_house = house
                        if mar_bday_house != short_house:
                            continue
                        
                        # Clue 21: Carol is the person who owns a Tesla Model 3.
                        carol_house = None
                        tesla_house = None
                        for house, attrs in assignment.items():
                            if attrs['name'] == 'Carol':
                                carol_house = house
                            if attrs['car'] == 'tesla model 3':
                                tesla_house = house
                        if carol_house != tesla_house:
                            continue
                        
                        # Clue 22: Eric is the person whose birthday is in January.
                        eric_house = None
                        jan_bday_house = None
                        for house, attrs in assignment.items():
                            if attrs['name'] == 'Eric':
                                eric_house = house
                            if attrs['birthday'] == 'jan':
                                jan_bday_house = house
                        if eric_house != jan_bday_house:
                            continue
                        
                        # If we get here, all constraints are satisfied
                        # Format the solution
                        solution = {
                            "solution": {
                                "header": ["House", "Name", "Birthday", "Food", "Height", "CarModel"],
                                "rows": []
                            }
                        }
                        
                        for house in sorted(assignment.keys()):
                            attrs = assignment[house]
                            row = [
                                str(house),
                                attrs['name'],
                                attrs['birthday'],
                                attrs['food'],
                                attrs['height'],
                                attrs['car']
                            ]
                            solution["solution"]["rows"].append(row)
                        
                        # Output the solution as JSON
                        print(json.dumps(solution, indent=2))
                        return
    
    # If no solution found
    print('{"solution": {"header": ["House", "Name", "Birthday", "Food", "Height", "CarModel"], "rows": []}}')

if __name__ == "__main__":
    main()