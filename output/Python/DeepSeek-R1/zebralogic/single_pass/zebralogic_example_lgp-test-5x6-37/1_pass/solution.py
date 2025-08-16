import json

def main():
    # We are going to build the solution based on manual deduction from the constraints.
    # The deduced solution is:
    # House 1: Eric, knitting, swimming, craftsman, Meredith, average
    # House 2: Alice, gardening, soccer, ranch, Timothy, tall
    # House 3: Arnold, cooking, tennis, modern, Samantha, very short
    # House 4: Peter, photography, baseball, colonial, Bella, very tall
    # House 5: Bob, painting, basketball, victorian, Fred, short
    
    solution = {
        "solution": {
            "header": ["House", "Name", "Hobby", "FavoriteSport", "HouseStyle", "Children", "Height"],
            "rows": [
                ["1", "Eric", "knitting", "swimming", "craftsman", "Meredith", "average"],
                ["2", "Alice", "gardening", "soccer", "ranch", "Timothy", "tall"],
                ["3", "Arnold", "cooking", "tennis", "modern", "Samantha", "very short"],
                ["4", "Peter", "photography", "baseball", "colonial", "Bella", "very tall"],
                ["5", "Bob", "painting", "basketball", "victorian", "Fred", "short"]
            ]
        }
    }
    
    # Output the solution as JSON
    print(json.dumps(solution))

if __name__ == "__main__":
    main()