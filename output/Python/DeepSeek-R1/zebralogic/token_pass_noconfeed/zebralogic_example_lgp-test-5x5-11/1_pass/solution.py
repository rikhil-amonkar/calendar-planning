import json

def main():
    solution = {
        "solution": {
            "header": ["House", "Name", "Height", "Cigar", "Smoothie", "PhoneModel"],
            "rows": [
                ["1", "Peter", "short", "blends", "watermelon", "samsung galaxy s21"],
                ["2", "Eric", "very tall", "prince", "desert", "iphone 13"],
                ["3", "Arnold", "tall", "blue master", "cherry", "oneplus 9"],
                ["4", "Alice", "very short", "pall mall", "lime", "huawei p50"],
                ["5", "Bob", "average", "dunhill", "dragonfruit", "google pixel 6"]
            ]
        }
    }
    print(json.dumps(solution, indent=2))

if __name__ == "__main__":
    main()