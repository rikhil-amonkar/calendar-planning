import json

def main():
    # Define the solution based on logical deduction from the constraints
    solution = {
        "solution": {
            "header": ["House", "Name", "HouseStyle", "HairColor", "Children", "BookGenre"],
            "rows": [
                ["1", "Arnold", "victorian", "red", "Meredith", "science fiction"],
                ["2", "Eric", "ranch", "black", "Fred", "mystery"],
                ["3", "Peter", "craftsman", "blonde", "Bella", "fantasy"],
                ["4", "Alice", "colonial", "brown", "Samantha", "romance"]
            ]
        }
    }
    
    # Output the solution as JSON
    print(json.dumps(solution, indent=2))

if __name__ == "__main__":
    main()