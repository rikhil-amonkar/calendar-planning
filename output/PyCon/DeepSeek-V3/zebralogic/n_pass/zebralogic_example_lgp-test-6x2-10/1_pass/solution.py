import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define variables: houses 1-6
    houses = [1, 2, 3, 4, 5, 6]
    
    # Define domains for names and music genres
    names = ["Arnold", "Eric", "Peter", "Alice", "Carol", "Bob"]
    genres = ["jazz", "pop", "classical", "rock", "hip hop", "country"]
    
    # Add variables for each house's name and music genre
    for house in houses:
        problem.addVariable(f"name_{house}", names)
        problem.addVariable(f"genre_{house}", genres)
    
    # All names and genres must be unique
    problem.addConstraint(AllDifferentConstraint(), [f"name_{house}" for house in houses])
    problem.addConstraint(AllDifferentConstraint(), [f"genre_{house}" for house in houses])
    
    # Clue 1: Bob is directly left of the person who loves jazz music
    for i in range(1, 6):
        problem.addConstraint(
            lambda bob_name, jazz_genre, bob_genre, jazz_name: 
                bob_name == "Bob" and jazz_genre == "jazz",
            [f"name_{i}", f"genre_{i+1}", f"genre_{i}", f"name_{i+1}"]
        )
    
    # Clue 2: Eric is somewhere to the left of the person who loves hip-hop music
    # This will be handled by clue 4 and clue 9
    
    # Clue 3: Carol is in the sixth house
    problem.addConstraint(lambda name: name == "Carol", ["name_6"])
    
    # Clue 4: Eric and the person who loves hip-hop music are next to each other
    # This will be handled by clue 9
    
    # Clue 5: The person who loves country music is Carol
    problem.addConstraint(
        lambda carol_name, country_genre: carol_name == "Carol" and country_genre == "country",
        ["name_6", "genre_6"]
    )
    
    # Clue 6: Arnold is not in the fifth house
    problem.addConstraint(lambda name: name != "Arnold", ["name_5"])
    
    # Clue 7: Arnold is somewhere to the right of the person who loves pop music
    # This will be handled by clue 8
    
    # Clue 8: The person who loves pop music is Peter
    for house in houses:
        problem.addConstraint(
            lambda name, genre: not (genre == "pop" and name != "Peter"),
            [f"name_{house}", f"genre_{house}"]
        )
    
    # Clue 9: The person who loves hip-hop music is in the third house
    problem.addConstraint(lambda genre: genre == "hip hop", ["genre_3"])
    
    # Clue 10: There is one house between Peter and Bob
    for i in range(1, 7):
        for j in range(1, 7):
            if abs(i - j) == 2:  # Exactly one house between them
                problem.addConstraint(
                    lambda name1, name2: (name1 == "Peter" and name2 == "Bob") or 
                                       (name1 == "Bob" and name2 == "Peter"),
                    [f"name_{i}", f"name_{j}"]
                )
    
    # Clue 11: The person who loves rock music is not in the fifth house
    problem.addConstraint(lambda genre: genre != "rock", ["genre_5"])
    
    # Additional constraints from clue combinations
    # From clue 4 and clue 9: Eric is next to house 3 (hip hop)
    problem.addConstraint(
        lambda name2, name4: name2 == "Eric" or name4 == "Eric",
        ["name_2", "name_4"]
    )
    
    # From clue 7 and clue 8: Arnold is to the right of Peter (who loves pop)
    for peter_house in houses:
        for arnold_house in houses:
            if arnold_house > peter_house:
                problem.addConstraint(
                    lambda name1, name2, genre: not (name1 == "Peter" and genre == "pop" and name2 == "Arnold"),
                    [f"name_{peter_house}", f"name_{arnold_house}", f"genre_{peter_house}"]
                )
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": ["House", "Name", "MusicGenre"], "rows": []}}
    
    # Take the first solution
    solution = solutions[0]
    
    # Build the result
    rows = []
    for house in houses:
        name = solution[f"name_{house}"]
        genre = solution[f"genre_{house}"]
        rows.append([str(house), name, genre])
    
    result = {
        "solution": {
            "header": ["House", "Name", "MusicGenre"],
            "rows": rows
        }
    }
    
    return result

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))