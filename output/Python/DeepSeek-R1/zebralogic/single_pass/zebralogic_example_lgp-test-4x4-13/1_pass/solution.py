import json

def main():
    # We have deduced the solution step by step using the constraints.
    houses = [
        ['Alice', 'prince', 'soccer', 'water'],   # House 1
        ['Arnold', 'blue master', 'tennis', 'coffee'],   # House 2
        ['Eric', 'dunhill', 'basketball', 'tea'],        # House 3
        ['Peter', 'pall mall', 'swimming', 'milk']       # House 4
    ]
    
    header = ["House", "Name", "Cigar", "FavoriteSport", "Drink"]
    rows = []
    for i in range(4):
        house_number = str(i + 1)
        row = [house_number] + houses[i]
        rows.append(row)
    
    solution_dict = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    
    print(json.dumps(solution_dict))

if __name__ == "__main__":
    main()