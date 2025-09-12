from z3 import *
import json

def main():
    # Define the categories
    names = ['Eric', 'Bob', 'Peter', 'Alice', 'Arnold', 'Carol']
    cars = ['ford f150', 'honda civic', 'toyota camry', 'tesla model 3', 'chevrolet silverado', 'bmw 3 series']
    mothers = ['Sarah', 'Penny', 'Holly', 'Aniya', 'Kailyn', 'Janelle']
    hobbies = ['photography', 'cooking', 'knitting', 'gardening', 'woodworking', 'painting']

    # Create variables for each value's house number
    name_houses = {name: Int(f'name_{name}_house') for name in names}
    car_houses = {car: Int(f'car_{car.replace(" ", "_")}_house') for car in cars}
    mother_houses = {mother: Int(f'mother_{mother}_house') for mother in mothers}
    hobby_houses = {hobby: Int(f'hobby_{hobby.replace(" ", "_")}_house') for hobby in hobbies}

    solver = Solver()

    # Add constraints for each category (1-6 and distinct)
    for category in [name_houses, car_houses, mother_houses, hobby_houses]:
        for var in category.values():
            solver.add(And(1 <= var, var <= 6))
        solver.add(Distinct(category.values()))

    # Add clues as constraints
    # Clue 1: Toyota Camry is in the sixth house.
    solver.add(car_houses['toyota camry'] == 6)

    # Clue 2: Carol is the photography enthusiast.
    solver.add(name_houses['Carol'] == hobby_houses['photography'])

    # Clue 3: Chevrolet Silverado owner's mother is Aniya.
    solver.add(car_houses['chevrolet silverado'] == mother_houses['Aniya'])

    # Clue 4: Chevrolet Silverado is not in house 2.
    solver.add(car_houses['chevrolet silverado'] != 2)

    # Clue 5: Ford F-150 owner's mother is Sarah.
    solver.add(car_houses['ford f150'] == mother_houses['Sarah'])

    # Clue 6: BMW 3 Series is Bob's car.
    solver.add(car_houses['bmw 3 series'] == name_houses['Bob'])

    # Clue 7: Kailyn is the mother in house 6.
    solver.add(mother_houses['Kailyn'] == 6)

    # Clue 8: Eric is directly left of the knitting hobbyist.
    solver.add(hobby_houses['knitting'] == name_houses['Eric'] + 1)

    # Clue 9: One house between Sarah (mother) and Toyota Camry (house 6).
    solver.add(Or(mother_houses['Sarah'] - 6 == 2, 6 - mother_houses['Sarah'] == 2))

    # Clue 10: Penny's mother is to the right of knitting hobbyist.
    solver.add(mother_houses['Penny'] > hobby_houses['knitting'])

    # Clue 11: Aniya's mother is to the right of Honda Civic owner.
    solver.add(mother_houses['Aniya'] > car_houses['honda civic'])

    # Clue 12: Alice is to the right of Ford F-150 owner.
    solver.add(name_houses['Alice'] > car_houses['ford f150'])

    # Clue 13: Eric's hobby is gardening.
    solver.add(name_houses['Eric'] == hobby_houses['gardening'])

    # Clue 14: Woodworking is to the left of knitting.
    solver.add(hobby_houses['woodworking'] < hobby_houses['knitting'])

    # Clue 15: One house between Sarah (mother) and cooking hobbyist.
    solver.add(Or(mother_houses['Sarah'] - hobby_houses['cooking'] == 2, hobby_houses['cooking'] - mother_houses['Sarah'] == 2))

    # Clue 16: Honda Civic is Arnold's car.
    solver.add(car_houses['honda civic'] == name_houses['Arnold'])

    # Clue 17: Holly's mother is directly left of knitting hobbyist.
    solver.add(hobby_houses['knitting'] == mother_houses['Holly'] + 1)

    # Check for solution
    if solver.check() == sat:
        model = solver.model()
        rows = []
        for house_num in range(1, 7):
            # Find name
            current_name = None
            for name in names:
                if model.evaluate(name_houses[name]) == house_num:
                    current_name = name
                    break
            # Find car
            current_car = None
            for car in cars:
                if model.evaluate(car_houses[car]) == house_num:
                    current_car = car
                    break
            # Find mother
            current_mother = None
            for mother in mothers:
                if model.evaluate(mother_houses[mother]) == house_num:
                    current_mother = mother
                    break
            # Find hobby
            current_hobby = None
            for hobby in hobbies:
                if model.evaluate(hobby_houses[hobby]) == house_num:
                    current_hobby = hobby
                    break
            rows.append([str(house_num), current_name, current_car, current_mother, current_hobby])
        solution = {
            "solution": {
                "header": ["House", "Name", "CarModel", "Mother", "Hobby"],
                "rows": rows
            }
        }
        print(json.dumps(solution, indent=2))
    else:
        print("No solution found.")

if __name__ == "__main__":
    main()