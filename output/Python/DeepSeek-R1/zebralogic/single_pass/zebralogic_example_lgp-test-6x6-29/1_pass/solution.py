import json

def main():
    solution = {
        "solution": {
            "header": ["House", "Name", "House Style", "Lunch", "Vacation", "Height", "Cigar"],
            "rows": [
                ["1", "Carol", "colonial", "stir fry", "city", "average", "dunhill"],
                ["2", "Bob", "craftsman", "soup", "mountain", "very tall", "yellow monster"],
                ["3", "Peter", "modern", "grilled cheese", "camping", "very short", "prince"],
                ["4", "Eric", "mediterranean", "pizza", "cultural", "short", "blends"],
                ["5", "Alice", "ranch", "spaghetti", "beach", "tall", "blue master"],
                ["6", "Arnold", "victorian", "stew", "cruise", "super tall", "pall mall"]
            ]
        }
    }
    print(json.dumps(solution))

if __name__ == "__main__":
    main()