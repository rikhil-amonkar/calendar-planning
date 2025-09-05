import json

def main():
    # Initialize houses with default unknown values
    houses = [
        {
            "House": "1",
            "Name": None,
            "Occupation": None,
            "Birthday": None,
            "HouseStyle": None,
            "Height": None,
            "Cigar": None
        },
        {
            "House": "2",
            "Name": None,
            "Occupation": None,
            "Birthday": None,
            "HouseStyle": None,
            "Height": None,
            "Cigar": None
        }
    ]
    
    # Apply clue 1: Engineer is in first house
    houses[0]["Occupation"] = "engineer"
    
    # Apply clue 3: Colonial house is engineer's house (so House 1)
    houses[0]["HouseStyle"] = "colonial"
    
    # Apply clue 4: Very short is engineer (so House 1)
    houses[0]["Height"] = "very short"
    
    # Apply clue 6: Engineer is Eric (so House 1)
    houses[0]["Name"] = "Eric"
    
    # Deduce remaining name for House 2
    houses[1]["Name"] = "Arnold"
    
    # Deduce occupation for House 2 (only doctor left)
    houses[1]["Occupation"] = "doctor"
    
    # Deduce height for House 2 (only short left)
    houses[1]["Height"] = "short"
    
    # Apply clue 5: Short person (House 2) likes Pall Mall
    houses[1]["Cigar"] = "pall mall"
    
    # Deduce cigar for House 1 (only prince left)
    houses[0]["Cigar"] = "prince"
    
    # Apply clue 2: April birthday and doctor are adjacent
    # Doctor is in House 2, so April must be in adjacent house (House 1)
    houses[0]["Birthday"] = "april"
    houses[1]["Birthday"] = "sept"
    
    # Deduce house style for House 2 (only victorian left)
    houses[1]["HouseStyle"] = "victorian"
    
    # Prepare output in required JSON format
    header = ["House", "Name", "Occupation", "Birthday", "HouseStyle", "Height", "Cigar"]
    rows = []
    for house in houses:
        row = [
            house["House"],
            house["Name"],
            house["Occupation"],
            house["Birthday"],
            house["HouseStyle"],
            house["Height"],
            house["Cigar"]
        ]
        rows.append(row)
    
    solution = {"solution": {"header": header, "rows": rows}}
    print(json.dumps(solution, indent=2))

if __name__ == "__main__":
    main()