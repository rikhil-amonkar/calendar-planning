import json
from z3 import *

def main():
    # Initialize solver
    s = Solver()
    
    # Define the attributes and their possible values (as indices)
    names = ['Eric', 'Bob', 'Peter', 'Alice', 'Arnold', 'Carol']
    cars = ['ford f150', 'honda civic', 'toyota camry', 'tesla model 3', 'chevrolet silverado', 'bmw 3 series']
    mothers = ['Sarah', 'Penny', 'Holly', 'Aniya', 'Kailyn', 'Janelle']
    hobbies = ['photography', 'cooking', 'knitting', 'gardening', 'woodworking', 'painting']
    
    # Create variables for each house and each category
    n = [Int('n_%d' % (i+1)) for i in range(6)]  # names
    c = [Int('c_%d' % (i+1)) for i in range(6)]  # cars
    m = [Int('m_%d' % (i+1)) for i in range(6)]  # mothers
    h = [Int('h_%d' % (i+1)) for i in range(6)]  # hobbies
    
    # Each attribute must be between 0 and 5
    for i in range(6):
        s.add(n[i] >= 0, n[i] <= 5)
        s.add(c[i] >= 0, c[i] <= 5)
        s.add(m[i] >= 0, m[i] <= 5)
        s.add(h[i] >= 0, h[i] <= 5)
    
    # All attributes in each category are distinct
    s.add(Distinct(n))
    s.add(Distinct(c))
    s.add(Distinct(m))
    s.add(Distinct(h))
    
    # Clue 1: The person who owns a Toyota Camry is in the sixth house.
    s.add(c[5] == 2)  # toyota camry index is 2
    
    # Clue 2: Carol is the photography enthusiast.
    # Carol is names index 5, photography is hobbies index 0
    s.add(Exists([i], And(i >= 0, i < 6, n[i] == 5, h[i] == 0)))
    
    # Clue 3: The person who owns a Chevrolet Silverado is the person whose mother's name is Aniya.
    # chevrolet silverado is cars index 4, Aniya is mothers index 3
    s.add(Exists([i], And(i >= 0, i < 6, c[i] == 4, m[i] == 3)))
    
    # Clue 4: The person who owns a Chevrolet Silverado is not in the second house.
    s.add(c[1] != 4)
    
    # Clue 5: The person who owns a Ford F-150 is the person whose mother's name is Sarah.
    # ford f150 is cars index 0, Sarah is mothers index 0
    s.add(Exists([i], And(i >= 0, i < 6, c[i] == 0, m[i] == 0)))
    
    # Clue 6: The person who owns a BMW 3 Series is Bob.
    # bmw 3 series is cars index 5, Bob is names index 1
    s.add(Exists([i], And(i >= 0, i < 6, c[i] == 5, n[i] == 1)))
    
    # Clue 7: The person whose mother's name is Kailyn is in the sixth house.
    s.add(m[5] == 4)  # Kailyn index is 4
    
    # Clue 8: Eric is directly left of the person who enjoys knitting.
    # Eric is names index 0, knitting is hobbies index 2
    s.add(Or([And(n[i] == 0, h[i+1] == 2) for i in range(5)]))
    
    # Clue 9: There is one house between the person whose mother's name is Sarah and the person who owns a Toyota Camry.
    # Sarah is mothers index 0, Toyota Camry is cars index 2
    s.add(Or([And(m[i] == 0, c[j] == 2, Or(i - j == 2, j - i == 2)) for i in range(6) for j in range(6)]))
    
    # Clue 10: The person whose mother's name is Penny is somewhere to the right of the person who enjoys knitting.
    # Penny is mothers index 1, knitting is hobbies index 2
    s.add(Exists([i, j], And(i >= 0, i < 6, j >= 0, j < 6, m[i] == 1, h[j] == 2, i > j)))
    
    # Clue 11: The person whose mother's name is Aniya is somewhere to the right of the person who owns a Honda Civic.
    # Aniya is mothers index 3, Honda Civic is cars index 1
    s.add(Exists([i, j], And(i >= 0, i < 6, j >= 0, j < 6, m[i] == 3, c[j] == 1, i > j)))
    
    # Clue 12: Alice is somewhere to the right of the person who owns a Ford F-150.
    # Alice is names index 3, Ford F-150 is cars index 0
    s.add(Exists([i, j], And(i >= 0, i < 6, j >= 0, j < 6, n[i] == 3, c[j] == 0, i > j)))
    
    # Clue 13: Eric is the person who enjoys gardening.
    # Eric is names index 0, gardening is hobbies index 3
    s.add(Exists([i], And(i >= 0, i < 6, n[i] == 0, h[i] == 3)))
    
    # Clue 14: The woodworking hobbyist is somewhere to the left of the person who enjoys knitting.
    # woodworking is hobbies index 4, knitting is hobbies index 2
    s.add(Exists([i, j], And(i >= 0, i < 6, j >= 0, j < 6, h[i] == 4, h[j] == 2, i < j)))
    
    # Clue 15: There is one house between the person whose mother's name is Sarah and the person who loves cooking.
    # Sarah is mothers index 0, cooking is hobbies index 1
    s.add(Or([And(m[i] == 0, h[j] == 1, Or(i - j == 2, j - i == 2)) for i in range(6) for j in range(6)]))
    
    # Clue 16: The person who owns a Honda Civic is Arnold.
    # Honda Civic is cars index 1, Arnold is names index 4
    s.add(Exists([i], And(i >= 0, i < 6, c[i] == 1, n[i] == 4)))
    
    # Clue 17: The person whose mother's name is Holly is directly left of the person who enjoys knitting.
    # Holly is mothers index 2, knitting is hobbies index 2
    s.add(Or([And(m[i] == 2, h[i+1] == 2) for i in range(5)]))
    
    # Check and get the solution
    if s.check() == sat:
        model = s.model()
        
        # Prepare the solution array
        solution = []
        for i in range(6):
            house_num = str(i+1)
            name_index = model.evaluate(n[i]).as_long()
            car_index = model.evaluate(c[i]).as_long()
            mother_index = model.evaluate(m[i]).as_long()
            hobby_index = model.evaluate(h[i]).as_long()
            
            row = [
                house_num,
                names[name_index],
                cars[car_index],
                mothers[mother_index],
                hobbies[hobby_index]
            ]
            solution.append(row)
        
        # Format the output as JSON
        output = {
            "solution": {
                "header": ["House", "Name", "CarModel", "Mother", "Hobby"],
                "rows": solution
            }
        }
        print(json.dumps(output, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()