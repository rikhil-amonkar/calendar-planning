import json

def main():
    # Initialize the attributes for 5 houses (0-indexed: house0, house1, ... house4)
    name = [None] * 5
    height = [None] * 5
    cigar = [None] * 5
    smoothie = [None] * 5
    phone = [None] * 5

    # Step 1: Assign Eric (house1, index1) with attributes from clues 6 and 15.
    name[1] = 'Eric'
    height[1] = 'very tall'
    phone[1] = 'iphone 13'

    # Step 2: Assign the house next to Eric (house2, index2) with cherry smoothie (clue9).
    smoothie[2] = 'cherry'

    # Step 3: Assign the house next to Eric (house2, index2) with blue master cigar (clue4).
    cigar[2] = 'blue master'

    # Step 4: Assign Alice two houses away from Eric (house3, index3) (clue2).
    name[3] = 'Alice'

    # Step 5: Assign Bob (house4, index4) with attributes from clues 10, 11, 5, and 14.
    name[4] = 'Bob'
    height[4] = 'average'
    cigar[4] = 'dunhill'
    smoothie[4] = 'dragonfruit'

    # Step 6: The only name left for house0 is Peter.
    name[0] = 'Peter'

    # Step 7: Assign Arnold to house2 (index2) and Huawei P50 to house3 (index4) (clue7).
    name[2] = 'Arnold'
    phone[3] = 'huawei p50'

    # Step 8: Assign very short height to Alice in house3 (index3) (clue17).
    height[3] = 'very short'

    # Step 9: Assign remaining attributes.
    height[0] = 'short'
    cigar[0] = 'blends'
    phone[0] = 'samsung galaxy s21'
    height[2] = 'tall'
    cigar[1] = 'prince'
    smoothie[1] = 'desert'
    cigar[3] = 'pall mall'
    smoothie[3] = 'lime'
    smoothie[0] = 'watermelon'
    phone[2] = 'oneplus 9'
    phone[4] = 'google pixel 6'

    # Create the solution rows
    header = ["House", "Name", "Height", "Cigar", "Smoothie", "PhoneModel"]
    rows = []
    for i in range(5):
        house_number = str(i+1)
        row = [house_number, name[i], height[i], cigar[i], smoothie[i], phone[i]]
        rows.append(row)

    # Format the solution as JSON
    solution_dict = {
        "solution": {
            "header": header,
            "rows": rows
        }
    }
    print(json.dumps(solution_dict, indent=2))

if __name__ == "__main__":
    main()