import z3
import json

def main():
    # Define the sorts for each category
    NameSort, (Eric, Bob, Peter, Alice, Arnold, Carol) = z3.EnumSort('NameSort', ['Eric', 'Bob', 'Peter', 'Alice', 'Arnold', 'Carol'])
    CarModelSort, (ford_f150, honda_civic, toyota_camry, tesla_model_3, chevrolet_silverado, bmw_3_series) = z3.EnumSort('CarModelSort', 
        ['ford f150', 'honda civic', 'toyota camry', 'tesla model 3', 'chevrolet silverado', 'bmw 3 series'])
    MotherSort, (Sarah, Penny, Holly, Aniya, Kailyn, Janelle) = z3.EnumSort('MotherSort', ['Sarah', 'Penny', 'Holly', 'Aniya', 'Kailyn', 'Janelle'])
    HobbySort, (photography, cooking, knitting, gardening, woodworking, painting) = z3.EnumSort('HobbySort', 
        ['photography', 'cooking', 'knitting', 'gardening', 'woodworking', 'painting'])
    
    # Create variables for each house
    names = [z3.Const(f'n_{i}', NameSort) for i in range(1, 7)]
    cars = [z3.Const(f'c_{i}', CarModelSort) for i in range(1, 7)]
    mothers = [z3.Const(f'm_{i}', MotherSort) for i in range(1, 7)]
    hobbies = [z3.Const(f'h_{i}', HobbySort) for i in range(1, 7)]
    
    solver = z3.Solver()
    
    # All attributes must be unique per category
    solver.add(z3.Distinct(names))
    solver.add(z3.Distinct(cars))
    solver.add(z3.Distinct(mothers))
    solver.add(z3.Distinct(hobbies))
    
    # Clue 1: Toyota Camry in sixth house
    solver.add(cars[5] == toyota_camry)
    
    # Clue 2: Carol enjoys photography
    solver.add(z3.Exists([z3.Const('x', z3.IntSort())], 
                         z3.And(z3.Const('x') >= 0, z3.Const('x') < 6, 
                                names[z3.Const('x')] == Carol, 
                                hobbies[z3.Const('x')] == photography)))
    
    # Clue 3: Chevrolet Silverado owner has mother Aniya
    for i in range(6):
        solver.add(z3.Implies(cars[i] == chevrolet_silverado, mothers[i] == Aniya))
    
    # Clue 4: Chevrolet Silverado not in second house
    solver.add(cars[1] != chevrolet_silverado)
    
    # Clue 5: Ford F-150 owner has mother Sarah
    for i in range(6):
        solver.add(z3.Implies(cars[i] == ford_f150, mothers[i] == Sarah))
    
    # Clue 6: BMW 3 Series owner is Bob
    for i in range(6):
        solver.add(z3.Implies(cars[i] == bmw_3_series, names[i] == Bob))
    
    # Clue 7: Mother Kailyn in sixth house
    solver.add(mothers[5] == Kailyn)
    
    # Clue 8: Eric directly left of knitting enthusiast
    for i in range(5):
        solver.add(z3.Implies(names[i] == Eric, hobbies[i+1] == knitting))
    solver.add(z3.Or([z3.And(names[i] == Eric, hobbies[i+1] == knitting) for i in range(5)]))
    
    # Clue 9: One house between mother Sarah and Toyota Camry (which is in house 6)
    # So mother Sarah must be in house 4 (since |4-6|=2 with one house between)
    solver.add(mothers[3] == Sarah)
    
    # Clue 10: Mother Penny right of knitting enthusiast
    for i in range(6):
        for j in range(i+1, 6):
            solver.add(z3.Implies(hobbies[i] == knitting, mothers[j] != Penny))
        solver.add(z3.Implies(hobbies[i] == knitting, z3.Or([mothers[j] == Penny for j in range(i+1, 6)])))
    
    # Clue 11: Mother Aniya right of Honda Civic owner
    for i in range(6):
        for j in range(i+1, 6):
            solver.add(z3.Implies(cars[i] == honda_civic, mothers[j] != Aniya))
        solver.add(z3.Implies(cars[i] == honda_civic, z3.Or([mothers[j] == Aniya for j in range(i+1, 6)])))
    
    # Clue 12: Alice right of Ford F-150 owner
    for i in range(6):
        for j in range(i+1, 6):
            solver.add(z3.Implies(cars[i] == ford_f150, names[j] != Alice))
        solver.add(z3.Implies(cars[i] == ford_f150, z3.Or([names[j] == Alice for j in range(i+1, 6)])))
    
    # Clue 13: Eric enjoys gardening
    for i in range(6):
        solver.add(z3.Implies(names[i] == Eric, hobbies[i] == gardening))
    
    # Clue 14: Woodworking left of knitting
    for i in range(6):
        for j in range(i):
            solver.add(z3.Implies(hobbies[i] == knitting, hobbies[j] != woodworking))
        solver.add(z3.Implies(hobbies[i] == knitting, z3.Or([hobbies[j] == woodworking for j in range(i)])))
    
    # Clue 15: One house between mother Sarah (house 4) and cooking enthusiast
    # So cooking must be in house 2 or 6 (|4-2|=2, |4-6|=2)
    solver.add(z3.Or(hobbies[1] == cooking, hobbies[5] == cooking))
    
    # Clue 16: Honda Civic owner is Arnold
    for i in range(6):
        solver.add(z3.Implies(cars[i] == honda_civic, names[i] == Arnold))
    
    # Clue 17: Mother Holly directly left of knitting enthusiast
    for i in range(5):
        solver.add(z3.Implies(mothers[i] == Holly, hobbies[i+1] == knitting))
    solver.add(z3.Or([z3.And(mothers[i] == Holly, hobbies[i+1] == knitting) for i in range(5)]))
    
    # Check and get the model
    if solver.check() == z3.sat:
        model = solver.model()
        
        # Extract values for each house
        result = []
        for i in range(6):
            house_num = str(i+1)
            name_val = str(model.eval(names[i]))
            car_val = str(model.eval(cars[i]))
            mother_val = str(model.eval(mothers[i]))
            hobby_val = str(model.eval(hobbies[i]))
            result.append([house_num, name_val, car_val, mother_val, hobby_val])
        
        # Format the output JSON
        output = {
            "solution": {
                "header": ["House", "Name", "CarModel", "Mother", "Hobby"],
                "rows": result
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()