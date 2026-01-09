import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define variables: houses 1-6
    houses = [1, 2, 3, 4, 5, 6]
    
    # Define domains
    names = ['Bob', 'Arnold', 'Carol', 'Alice', 'Peter', 'Eric']
    genres = ['romance', 'historical fiction', 'biography', 'mystery', 'fantasy', 'science fiction']
    occupations = ['artist', 'doctor', 'nurse', 'engineer', 'teacher', 'lawyer']
    
    # Add variables for each attribute
    problem.addVariables(['name'] + names, houses)
    problem.addVariables(['genre'] + genres, houses)
    problem.addVariables(['occupation'] + occupations, houses)
    
    # All attributes must have unique houses
    problem.addConstraint(AllDifferentConstraint(), names)
    problem.addConstraint(AllDifferentConstraint(), genres)
    problem.addConstraint(AllDifferentConstraint(), occupations)
    
    # Clue 1: Alice is the person who loves fantasy books
    problem.addConstraint(lambda alice, fantasy: alice == fantasy, ('Alice', 'fantasy'))
    
    # Clue 2: The person who loves mystery books and Bob are next to each other
    problem.addConstraint(lambda mystery, bob: abs(mystery - bob) == 1, ('mystery', 'Bob'))
    
    # Clue 3: Carol is the person who loves mystery books
    problem.addConstraint(lambda carol, mystery: carol == mystery, ('Carol', 'mystery'))
    
    # Clue 4: The person who is a lawyer is the person who loves fantasy books
    problem.addConstraint(lambda lawyer, fantasy: lawyer == fantasy, ('lawyer', 'fantasy'))
    
    # Clue 5: Bob is not in the fifth house
    problem.addConstraint(lambda bob: bob != 5, ('Bob',))
    
    # Clue 6: Arnold is somewhere to the left of the person who is an engineer
    problem.addConstraint(lambda arnold, engineer: arnold < engineer, ('Arnold', 'engineer'))
    
    # Clue 7: The person who is a nurse is directly left of Alice
    problem.addConstraint(lambda nurse, alice: nurse == alice - 1, ('nurse', 'Alice'))
    
    # Clue 8: The person who loves biography books is the person who is a teacher
    problem.addConstraint(lambda biography, teacher: biography == teacher, ('biography', 'teacher'))
    
    # Clue 9: The person who loves historical fiction books is somewhere to the left of the person who is a teacher
    problem.addConstraint(lambda hist_fiction, teacher: hist_fiction < teacher, ('historical fiction', 'teacher'))
    
    # Clue 10: The person who is a doctor is in the first house
    problem.addConstraint(lambda doctor: doctor == 1, ('doctor',))
    
    # Clue 11: The person who loves science fiction books is the person who is an artist
    problem.addConstraint(lambda scifi, artist: scifi == artist, ('science fiction', 'artist'))
    
    # Clue 12: Eric is in the third house
    problem.addConstraint(lambda eric: eric == 3, ('Eric',))
    
    # Clue 13: The person who loves mystery books is not in the fifth house
    problem.addConstraint(lambda mystery: mystery != 5, ('mystery',))
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "BookGenre", "Occupation"], "rows": []}}
    
    solution = solutions[0]
    
    # Create the result structure
    result = {
        "solution": {
            "header": ["House", "Name", "BookGenre", "Occupation"],
            "rows": []
        }
    }
    
    # Build the rows for each house
    for house in houses:
        # Find name for this house
        name = next(n for n in names if solution[n] == house)
        
        # Find genre for this house
        genre = next(g for g in genres if solution[g] == house)
        
        # Find occupation for this house
        occupation = next(o for o in occupations if solution[o] == house)
        
        result["solution"]["rows"].append([str(house), name, genre, occupation])
    
    return result

if __name__ == "__main__":
    solution = solve_puzzle()
    print(json.dumps(solution, indent=2))