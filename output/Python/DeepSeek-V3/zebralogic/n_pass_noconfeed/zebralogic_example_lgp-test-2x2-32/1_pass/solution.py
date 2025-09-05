import json

def main():
    # Define the problem parameters
    houses = [1, 2]
    names = ["Eric", "Arnold"]
    book_genres = ["science fiction", "mystery"]
    
    # Initialize all possible assignments
    for name_assignment in [(names[0], names[1]), (names[1], names[0])]:
        for book_assignment in [(book_genres[0], book_genres[1]), (book_genres[1], book_genres[0])]:
            # Check clue 1: Eric is directly left of the person who loves mystery books
            valid = True
            
            # Find Eric's position
            eric_position = None
            mystery_position = None
            
            for i, name in enumerate(name_assignment):
                if name == "Eric":
                    eric_position = i
                if book_assignment[i] == "mystery":
                    mystery_position = i
            
            # Check if Eric is directly left of mystery lover
            if eric_position is not None and mystery_position is not None:
                if mystery_position - eric_position != 1:
                    valid = False
            else:
                valid = False
            
            if valid:
                # Format the solution
                solution = {
                    "solution": {
                        "header": ["House", "Name", "BookGenre"],
                        "rows": []
                    }
                }
                
                for i in range(len(houses)):
                    row = [str(i + 1), name_assignment[i], book_assignment[i]]
                    solution["solution"]["rows"].append(row)
                
                # Output as JSON
                print(json.dumps(solution, indent=2))
                return
    
    # If no solution found (shouldn't happen with valid constraints)
    print(json.dumps({"solution": {"header": ["House", "Name", "BookGenre"], "rows": []}}))

if __name__ == "__main__":
    main()