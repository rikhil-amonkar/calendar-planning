from constraint import Problem
import json

def solve_puzzle():
    problem = Problem()
    
    houses = [1, 2, 3, 4, 5, 6]
    
    # Define variables
    names = ['Eric', 'Bob', 'Peter', 'Alice', 'Arnold', 'Carol']
    cars = ['ford f150', 'honda civic', 'toyota camry', 'tesla model 3', 'chevrolet silverado', 'bmw 3 series']
    mothers = ['Sarah', 'Penny', 'Holly', 'Aniya', 'Kailyn', 'Janelle']
    hobbies = ['photography', 'cooking', 'knitting', 'gardening', 'woodworking', 'painting']
    
    # Add variables for each attribute
    problem.addVariables(['name'], [names])
    problem.addVariables(['car'], [cars])
    problem.addVariables(['mother'], [mothers])
    problem.addVariables(['hobby'], [hobbies])
    
    # Add all constraints
    problem.addConstraint(lambda n, c, m, h: len(set(n)) == 6 and len(set(c)) == 6 and len(set(m)) == 6 and len(set(h)) == 6,
                         ['name', 'car', 'mother', 'hobby'])
    
    # Clue 1: Toyota Camry in sixth house
    problem.addConstraint(lambda c: c[5] == 'toyota camry', ['car'])
    
    # Clue 2: Carol is photography enthusiast
    problem.addConstraint(lambda n, h: h[n.index('Carol')] == 'photography', ['name', 'hobby'])
    
    # Clue 3: Chevrolet Silverado owner has mother Aniya
    problem.addConstraint(lambda c, m: m[c.index('chevrolet silverado')] == 'Aniya', ['car', 'mother'])
    
    # Clue 4: Chevrolet Silverado not in second house
    problem.addConstraint(lambda c: c[1] != 'chevrolet silverado', ['car'])
    
    # Clue 5: Ford F-150 owner has mother Sarah
    problem.addConstraint(lambda c, m: m[c.index('ford f150')] == 'Sarah', ['car', 'mother'])
    
    # Clue 6: BMW 3 Series owner is Bob
    problem.addConstraint(lambda n, c: n[c.index('bmw 3 series')] == 'Bob', ['name', 'car'])
    
    # Clue 7: Mother Kailyn in sixth house
    problem.addConstraint(lambda m: m[5] == 'Kailyn', ['mother'])
    
    # Clue 8: Eric is directly left of knitting enthusiast
    problem.addConstraint(lambda n, h: h[n.index('Eric') + 1] == 'knitting' if 'Eric' in n and n.index('Eric') < 5 else False, ['name', 'hobby'])
    
    # Clue 9: One house between mother Sarah and Toyota Camry
    problem.addConstraint(lambda m, c: abs(m.index('Sarah') - c.index('toyota camry')) == 2, ['mother', 'car'])
    
    # Clue 10: Mother Penny is right of knitting enthusiast
    problem.addConstraint(lambda m, h: m.index('Penny') > h.index('knitting'), ['mother', 'hobby'])
    
    # Clue 11: Mother Aniya is right of Honda Civic owner
    problem.addConstraint(lambda m, c: m.index('Aniya') > c.index('honda civic'), ['mother', 'car'])
    
    # Clue 12: Alice is right of Ford F-150 owner
    problem.addConstraint(lambda n, c: n.index('Alice') > c.index('ford f150'), ['name', 'car'])
    
    # Clue 13: Eric enjoys gardening
    problem.addConstraint(lambda n, h: h[n.index('Eric')] == 'gardening', ['name', 'hobby'])
    
    # Clue 14: Woodworking is left of knitting
    problem.addConstraint(lambda h: h.index('woodworking') < h.index('knitting'), ['hobby'])
    
    # Clue 15: One house between mother Sarah and cooking enthusiast
    problem.addConstraint(lambda m, h: abs(m.index('Sarah') - h.index('cooking')) == 2, ['mother', 'hobby'])
    
    # Clue 16: Honda Civic owner is Arnold
    problem.addConstraint(lambda n, c: n[c.index('honda civic')] == 'Arnold', ['name', 'car'])
    
    # Clue 17: Mother Holly is directly left of knitting enthusiast
    problem.addConstraint(lambda m, h: m.index('Holly') + 1 == h.index('knitting'), ['mother', 'hobby'])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "CarModel", "Mother", "Hobby"], "rows": []}}
    
    solution = solutions[0]
    names = solution['name']
    cars = solution['car']
    mothers = solution['mother']
    hobbies = solution['hobby']
    
    rows = []
    for i in range(6):
        rows.append([str(i+1), names[i], cars[i], mothers[i], hobbies[i]])
    
    return {
        "solution": {
            "header": ["House", "Name", "CarModel", "Mother", "Hobby"],
            "rows": rows
        }
    }

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))