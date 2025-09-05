import json

def main():
    # Initialize the solution grid with house numbers
    houses = [
        ["1", None, None, None],
        ["2", None, None, None],
        ["3", None, None, None],
        ["4", None, None, None],
        ["5", None, None, None],
        ["6", None, None, None]
    ]
    
    # Assign values based on deduced solution
    houses[0][1] = "Bob"
    houses[0][2] = "Penny"
    houses[0][3] = "dog"
    
    houses[1][1] = "Peter"
    houses[1][2] = "Sarah"
    houses[1][3] = "fish"
    
    houses[2][1] = "Arnold"
    houses[2][2] = "Janelle"
    houses[2][3] = "cat"
    
    houses[3][1] = "Alice"
    houses[3][2] = "Holly"
    houses[3][3] = "bird"
    
    houses[4][1] = "Carol"
    houses[4][2] = "Aniya"
    houses[4][3] = "hamster"
    
    houses[5][1] = "Eric"
    houses[5][2] = "Kailyn"
    houses[5][3] = "rabbit"
    
    # Prepare the output dictionary
    output = {
        "solution": {
            "header": ["House", "Name", "Mother", "Pet"],
            "rows": houses
        }
    }
    
    # Output as JSON
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()