import json
from constraint import Problem, AllDifferentConstraint

def solve_puzzle():
    problem = Problem()
    
    # Define variables: houses 1-6
    houses = [1, 2, 3, 4, 5, 6]
    
    # Define domains for each attribute
    names = ['Eric', 'Alice', 'Arnold', 'Carol', 'Peter', 'Bob']
    styles = ['mediterranean', 'modern', 'craftsman', 'ranch', 'colonial', 'victorian']
    genres = ['country', 'hip hop', 'pop', 'jazz', 'classical', 'rock']
    hobbies = ['cooking', 'painting', 'photography', 'woodworking', 'gardening', 'knitting']
    
    # Add variables for each attribute per house
    problem.addVariables(["name"] + houses, names)
    problem.addVariables(["style"] + houses, styles)
    problem.addVariables(["genre"] + houses, genres)
    problem.addVariables(["hobby"] + houses, hobbies)
    
    # All attributes must be different
    problem.addConstraint(AllDifferentConstraint(), ["name" + str(i) for i in houses])
    problem.addConstraint(AllDifferentConstraint(), ["style" + str(i) for i in houses])
    problem.addConstraint(AllDifferentConstraint(), ["genre" + str(i) for i in houses])
    problem.addConstraint(AllDifferentConstraint(), ["hobby" + str(i) for i in houses])
    
    # Clue 1: The person who loves rock music is in the fifth house.
    problem.addConstraint(lambda genre5: genre5 == 'rock', ['genre5'])
    
    # Clue 2: The person who loves classical music and the woodworking hobbyist are next to each other.
    def adjacent_classical_woodworking(genre1, genre2, genre3, genre4, genre5, genre6,
                                      hobby1, hobby2, hobby3, hobby4, hobby5, hobby6):
        classical_house = None
        woodworking_house = None
        
        for i, genre in enumerate([genre1, genre2, genre3, genre4, genre5, genre6], 1):
            if genre == 'classical':
                classical_house = i
        for i, hobby in enumerate([hobby1, hobby2, hobby3, hobby4, hobby5, hobby6], 1):
            if hobby == 'woodworking':
                woodworking_house = i
        
        return abs(classical_house - woodworking_house) == 1
    
    problem.addConstraint(adjacent_classical_woodworking, 
                         ['genre1', 'genre2', 'genre3', 'genre4', 'genre5', 'genre6',
                          'hobby1', 'hobby2', 'hobby3', 'hobby4', 'hobby5', 'hobby6'])
    
    # Clue 3: The person in a Mediterranean-style villa is the person who loves hip-hop music.
    def mediterranean_hiphop(style1, style2, style3, style4, style5, style6,
                            genre1, genre2, genre3, genre4, genre5, genre6):
        for i in range(1, 7):
            style = locals()[f'style{i}']
            genre = locals()[f'genre{i}']
            if style == 'mediterranean':
                return genre == 'hip hop'
        return False
    
    problem.addConstraint(mediterranean_hiphop,
                         ['style1', 'style2', 'style3', 'style4', 'style5', 'style6',
                          'genre1', 'genre2', 'genre3', 'genre4', 'genre5', 'genre6'])
    
    # Clue 4: There are two houses between Arnold and the person residing in a Victorian house.
    def two_houses_between_arnold_victorian(name1, name2, name3, name4, name5, name6,
                                           style1, style2, style3, style4, style5, style6):
        arnold_house = None
        victorian_house = None
        
        for i in range(1, 7):
            name = locals()[f'name{i}']
            style = locals()[f'style{i}']
            if name == 'Arnold':
                arnold_house = i
            if style == 'victorian':
                victorian_house = i
        
        return abs(arnold_house - victorian_house) == 3
    
    problem.addConstraint(two_houses_between_arnold_victorian,
                         ['name1', 'name2', 'name3', 'name4', 'name5', 'name6',
                          'style1', 'style2', 'style3', 'style4', 'style5', 'style6'])
    
    # Clue 5: The person who loves jazz music is directly left of Eric.
    def jazz_left_of_eric(genre1, genre2, genre3, genre4, genre5, genre6,
                         name1, name2, name3, name4, name5, name6):
        for i in range(1, 6):
            if locals()[f'genre{i}'] == 'jazz' and locals()[f'name{i+1}'] == 'Eric':
                return True
        return False
    
    problem.addConstraint(jazz_left_of_eric,
                         ['genre1', 'genre2', 'genre3', 'genre4', 'genre5', 'genre6',
                          'name1', 'name2', 'name3', 'name4', 'name5', 'name6'])
    
    # Clue 6: The person who loves hip-hop music is somewhere to the left of the person who enjoys knitting.
    def hiphop_left_of_knitting(genre1, genre2, genre3, genre4, genre5, genre6,
                               hobby1, hobby2, hobby3, hobby4, hobby5, hobby6):
        hiphop_house = None
        knitting_house = None
        
        for i in range(1, 7):
            if locals()[f'genre{i}'] == 'hip hop':
                hiphop_house = i
            if locals()[f'hobby{i}'] == 'knitting':
                knitting_house = i
        
        return hiphop_house < knitting_house
    
    problem.addConstraint(hiphop_left_of_knitting,
                         ['genre1', 'genre2', 'genre3', 'genre4', 'genre5', 'genre6',
                          'hobby1', 'hobby2', 'hobby3', 'hobby4', 'hobby5', 'hobby6'])
    
    # Clue 7: Carol is the person who loves hip-hop music.
    def carol_hiphop(name1, name2, name3, name4, name5, name6,
                    genre1, genre2, genre3, genre4, genre5, genre6):
        for i in range(1, 7):
            if locals()[f'name{i}'] == 'Carol':
                return locals()[f'genre{i}'] == 'hip hop'
        return False
    
    problem.addConstraint(carol_hiphop,
                         ['name1', 'name2', 'name3', 'name4', 'name5', 'name6',
                          'genre1', 'genre2', 'genre3', 'genre4', 'genre5', 'genre6'])
    
    # Clue 8: The person in a Craftsman-style house is Arnold.
    def craftsman_arnold(style1, style2, style3, style4, style5, style6,
                        name1, name2, name3, name4, name5, name6):
        for i in range(1, 7):
            if locals()[f'style{i}'] == 'craftsman':
                return locals()[f'name{i}'] == 'Arnold'
        return False
    
    problem.addConstraint(craftsman_arnold,
                         ['style1', 'style2', 'style3', 'style4', 'style5', 'style6',
                          'name1', 'name2', 'name3', 'name4', 'name5', 'name6'])
    
    # Clue 9: The person in a ranch-style home is Eric.
    def ranch_eric(style1, style2, style3, style4, style5, style6,
                  name1, name2, name3, name4, name5, name6):
        for i in range(1, 7):
            if locals()[f'style{i}'] == 'ranch':
                return locals()[f'name{i}'] == 'Eric'
        return False
    
    problem.addConstraint(ranch_eric,
                         ['style1', 'style2', 'style3', 'style4', 'style5', 'style6',
                          'name1', 'name2', 'name3', 'name4', 'name5', 'name6'])
    
    # Clue 10: The woodworking hobbyist is the person residing in a Victorian house.
    def woodworking_victorian(hobby1, hobby2, hobby3, hobby4, hobby5, hobby6,
                             style1, style2, style3, style4, style5, style6):
        for i in range(1, 7):
            if locals()[f'hobby{i}'] == 'woodworking':
                return locals()[f'style{i}'] == 'victorian'
        return False
    
    problem.addConstraint(woodworking_victorian,
                         ['hobby1', 'hobby2', 'hobby3', 'hobby4', 'hobby5', 'hobby6',
                          'style1', 'style2', 'style3', 'style4', 'style5', 'style6'])
    
    # Clue 11: The person who loves country music is in the first house.
    problem.addConstraint(lambda genre1: genre1 == 'country', ['genre1'])
    
    # Clue 12: There is one house between the person who paints as a hobby and the person living in a colonial-style house.
    def one_house_between_painting_colonial(hobby1, hobby2, hobby3, hobby4, hobby5, hobby6,
                                           style1, style2, style3, style4, style5, style6):
        painting_house = None
        colonial_house = None
        
        for i in range(1, 7):
            if locals()[f'hobby{i}'] == 'painting':
                painting_house = i
            if locals()[f'style{i}'] == 'colonial':
                colonial_house = i
        
        return abs(painting_house - colonial_house) == 2
    
    problem.addConstraint(one_house_between_painting_colonial,
                         ['hobby1', 'hobby2', 'hobby3', 'hobby4', 'hobby5', 'hobby6',
                          'style1', 'style2', 'style3', 'style4', 'style5', 'style6'])
    
    # Clue 13: Alice is the photography enthusiast.
    def alice_photography(name1, name2, name3, name4, name5, name6,
                         hobby1, hobby2, hobby3, hobby4, hobby5, hobby6):
        for i in range(1, 7):
            if locals()[f'name{i}'] == 'Alice':
                return locals()[f'hobby{i}'] == 'photography'
        return False
    
    problem.addConstraint(alice_photography,
                         ['name1', 'name2', 'name3', 'name4', 'name5', 'name6',
                          'hobby1', 'hobby2', 'hobby3', 'hobby4', 'hobby5', 'hobby6'])
    
    # Clue 14: The person who enjoys gardening is Eric.
    def eric_gardening(name1, name2, name3, name4, name5, name6,
                      hobby1, hobby2, hobby3, hobby4, hobby5, hobby6):
        for i in range(1, 7):
            if locals()[f'name{i}'] == 'Eric':
                return locals()[f'hobby{i}'] == 'gardening'
        return False
    
    problem.addConstraint(eric_gardening,
                         ['name1', 'name2', 'name3', 'name4', 'name5', 'name6',
                          'hobby1', 'hobby2', 'hobby3', 'hobby4', 'hobby5', 'hobby6'])
    
    # Clue 15: Bob is in the third house.
    problem.addConstraint(lambda name3: name3 == 'Bob', ['name3'])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"solution": {"header": [], "rows": []}}
    
    # Take the first solution
    solution = solutions[0]
    
    # Build the result
    header = ["House", "Name", "HouseStyle", "MusicGenre", "Hobby"]
    rows = []
    
    for house in houses:
        row = [
            str(house),
            solution[f"name{house}"],
            solution[f"style{house}"],
            solution[f"genre{house}"],
            solution[f"hobby{house}"]
        ]
        rows.append(row)
    
    return {
        "solution": {
            "header": header,
            "rows": rows
        }
    }

if __name__ == "__main__":
    result = solve_puzzle()
    print(json.dumps(result, indent=2))