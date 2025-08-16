import json

def main():
    # Create the solution data structure
    solution = {
        "solution": {
            "header": ["House", "Name", "Pet", "HouseStyle", "Birthday"],
            "rows": [
                ["1", "Bob", "cat", "mediterranean", "feb"],
                ["2", "Peter", "rabbit", "colonial", "may"],
                ["3", "Carol", "bird", "victorian", "mar"],
                ["4", "Arnold", "dog", "craftsman", "jan"],
                ["5", "Alice", "fish", "modern", "april"],
                ["6", "Eric", "hamster", "ranch", "sept"]
            ]
        }
    }
    
    # Output the solution as JSON
    print(json.dumps(solution))

if __name__ == "__main__":
    main()