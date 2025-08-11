import json

def main():
    solution = {
        "solution": {
            "header": ["House", "name", "house_style", "mother", "phone", "drink", "animal"],
            "rows": [
                ["1", "Peter", "victorian", "Aniya", "huawei p50", "root beer", "cat"],
                ["2", "Arnold", "ranch", "Kailyn", "iphone 13", "milk", "dog"],
                ["3", "Eric", "modern", "Penny", "oneplus 9", "coffee", "horse"],
                ["4", "Bob", "craftsman", "Holly", "google pixel 6", "tea", "bird"],
                ["5", "Alice", "colonial", "Janelle", "samsung galaxy s21", "water", "fish"]
            ]
        }
    }
    print(json.dumps(solution, indent=2))

if __name__ == "__main__":
    main()