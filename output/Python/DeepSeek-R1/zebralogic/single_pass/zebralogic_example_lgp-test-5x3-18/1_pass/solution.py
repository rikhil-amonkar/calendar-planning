import json

def main():
    # Initialize arrays for attributes
    names = [None] * 5
    flowers = [None] * 5
    animals = [None] * 5

    # Apply clues
    names[1] = 'Alice'             # Clue 1: Alice in second house
    animals[2] = 'horse'           # Clue 8: Alice left of horse keeper
    names[2] = 'Eric'              # Clue 5: Horse keeper is Eric
    names[4] = 'Bob'               # Deduction: Bob in fifth house
    animals[3] = 'fish'            # Clue 7: Fish left of Bob
    flowers[3] = 'daffodils'       # Clue 4: Fish enthusiast loves daffodils
    animals[1] = 'dog'             # Clue 6: Dog in second house (two houses from Bob)
    animals[0] = 'bird'            # Only remaining animals: bird and cat
    animals[4] = 'cat'             # Clue 10: Cat not in first house
    flowers[0] = 'lilies'          # Clue 2: Bird keeper loves lilies
    flowers[1] = 'carnations'      # Clue 9: Carnations left of tulips
    flowers[2] = 'tulips'          # Clue 9: Tulips right of carnations
    flowers[4] = 'roses'           # Last remaining flower
    names[3] = 'Peter'             # Clue 3: Peter right of tulips lover
    names[0] = 'Arnold'            # Last remaining name

    # Prepare solution structure
    header = ["House", "Name", "Flower", "Animal"]
    rows = []
    for i in range(5):
        house_num = str(i + 1)
        row = [house_num, names[i], flowers[i], animals[i]]
        rows.append(row)
    
    solution_dict = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    
    print(json.dumps(solution_dict, indent=2))

if __name__ == '__main__':
    main()