import json

def main():
    # Define the solution based on logical deduction
    solution = {
        "header": ["House", "Name", "Animal", "Occupation", "FavoriteSport", "Height"],
        "rows": [
            ["1", "Peter", "bird", "nurse", "baseball", "very tall"],
            ["2", "Eric", "dog", "engineer", "swimming", "average"],
            ["3", "Alice", "rabbit", "artist", "volleyball", "tall"],
            ["4", "Bob", "horse", "teacher", "tennis", "very short"],
            ["5", "Carol", "fish", "lawyer", "soccer", "super tall"],
            ["6", "Arnold", "cat", "doctor", "basketball", "short"]
        ]
    }
    
    # Output the solution as JSON
    print(json.dumps({"solution": solution}))

if __name__ == "__main__":
    main()