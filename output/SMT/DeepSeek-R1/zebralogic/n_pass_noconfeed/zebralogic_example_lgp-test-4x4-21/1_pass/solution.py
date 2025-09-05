from z3 import *

def main():
    s = Solver()
    
    # Define the variables for each attribute's house
    Eric_house = Int('Eric_house')
    Peter_house = Int('Peter_house')
    Alice_house = Int('Alice_house')
    Arnold_house = Int('Arnold_house')
    
    tesla_house = Int('tesla_house')
    honda_house = Int('honda_house')
    toyota_house = Int('toyota_house')
    ford_house = Int('ford_house')
    
    jan_house = Int('jan_house')
    april_house = Int('april_house')
    sept_house = Int('sept_house')
    feb_house = Int('feb_house')
    
    painting_house = Int('painting_house')
    cooking_house = Int('cooking_house')
    gardening_house = Int('gardening_house')
    photography_house = Int('photography_house')
    
    # All houses must be between 1 and 4
    houses = [Eric_house, Peter_house, Alice_house, Arnold_house,
              tesla_house, honda_house, toyota_house, ford_house,
              jan_house, april_house, sept_house, feb_house,
              painting_house, cooking_house, gardening_house, photography_house]
    
    for h in houses:
        s.add(h >= 1, h <= 4)
    
    # Each attribute category must have distinct houses
    s.add(Distinct([Eric_house, Peter_house, Alice_house, Arnold_house]))
    s.add(Distinct([tesla_house, honda_house, toyota_house, ford_house]))
    s.add(Distinct([jan_house, april_house, sept_house, feb_house]))
    s.add(Distinct([painting_house, cooking_house, gardening_house, photography_house]))
    
    # Add the clues
    s.add(jan_house != 2)  # Clue 1
    s.add(photography_house < Eric_house)  # Clue 2
    s.add(photography_house < Peter_house)  # Clue 3
    s.add(honda_house + 1 == tesla_house)  # Clue 4
    s.add(Or(tesla_house - gardening_house == 2, gardening_house - tesla_house == 2))  # Clue 5
    s.add(tesla_house == Arnold_house)  # Clue 6
    s.add(feb_house == cooking_house)  # Clue 7
    s.add(toyota_house == Peter_house)  # Clue 8
    s.add(april_house == Arnold_house)  # Clue 9
    s.add(Alice_house == photography_house)  # Clue 10
    s.add(Peter_house == jan_house)  # Clue 11
    
    if s.check() == sat:
        m = s.model()
        # Create a mapping from house number to attributes
        houses = {1: {}, 2: {}, 3: {}, 4: {}}
        
        # Helper function to get house number from model
        def get_house(var):
            return m[var].as_long()
        
        # Assign names
        houses[get_house(Eric_house)]['Name'] = 'Eric'
        houses[get_house(Peter_house)]['Name'] = 'Peter'
        houses[get_house(Alice_house)]['Name'] = 'Alice'
        houses[get_house(Arnold_house)]['Name'] = 'Arnold'
        
        # Assign car models
        houses[get_house(tesla_house)]['CarModel'] = 'tesla model 3'
        houses[get_house(honda_house)]['CarModel'] = 'honda civic'
        houses[get_house(toyota_house)]['CarModel'] = 'toyota camry'
        houses[get_house(ford_house)]['CarModel'] = 'ford f150'
        
        # Assign birthdays
        houses[get_house(jan_house)]['Birthday'] = 'jan'
        houses[get_house(april_house)]['Birthday'] = 'april'
        houses[get_house(sept_house)]['Birthday'] = 'sept'
        houses[get_house(feb_house)]['Birthday'] = 'feb'
        
        # Assign hobbies
        houses[get_house(painting_house)]['Hobby'] = 'painting'
        houses[get_house(cooking_house)]['Hobby'] = 'cooking'
        houses[get_house(gardening_house)]['Hobby'] = 'gardening'
        houses[get_house(photography_house)]['Hobby'] = 'photography'
        
        # Prepare the output JSON structure
        header = ["House", "Name", "CarModel", "Birthday", "Hobby"]
        rows = []
        for i in range(1, 5):
            house_data = houses[i]
            row = [str(i), house_data['Name'], house_data['CarModel'], house_data['Birthday'], house_data['Hobby']]
            rows.append(row)
        
        solution = {
            "solution": {
                "header": header,
                "rows": rows
            }
        }
        
        import json
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()