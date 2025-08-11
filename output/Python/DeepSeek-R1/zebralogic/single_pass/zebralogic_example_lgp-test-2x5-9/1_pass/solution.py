import json

def main():
    # Initialize the houses as dictionaries with the correct attribute names
    house1 = {
        "Name": None,
        "Favorite Book Genres": None,
        "Vacation Type": None,
        "Animals": None,
        "Favorite Music Genres": None
    }
    house2 = {
        "Name": None,
        "Favorite Book Genres": None,
        "Vacation Type": None,
        "Animals": None,
        "Favorite Music Genres": None
    }
    
    # Apply clue 5: The person who loves mystery books is in the first house.
    house1["Favorite Book Genres"] = "mystery"
    
    # Apply clue 4: The cat lover is not in the second house (so must be in first)
    house1["Animals"] = "cat"
    
    # Apply clue 3: The person who loves rock music is the person who loves mystery books.
    # Since mystery books are in house1, rock music must be in house1.
    house1["Favorite Music Genres"] = "rock"
    
    # The remaining book genre for house2 is science fiction
    house2["Favorite Book Genres"] = "science fiction"
    
    # The remaining music genre for house2 is pop
    house2["Favorite Music Genres"] = "pop"
    
    # The remaining animal for house2 is horse
    house2["Animals"] = "horse"
    
    # Apply clue 2: The person who loves pop music is the person who loves beach vacations.
    # Since house2 has pop music, house2 must have beach vacations.
    house2["Vacation Type"] = "beach"
    
    # Apply clue 1: The person who loves beach vacations is Eric.
    # Since house2 has beach vacations, Eric must be in house2.
    house2["Name"] = "Eric"
    
    # The remaining vacation type for house1 is mountain
    house1["Vacation Type"] = "mountain"
    
    # The remaining name for house1 is Arnold
    house1["Name"] = "Arnold"
    
    # Prepare the solution dictionary
    header = ["House", "Name", "Favorite Book Genres", "Vacation Type", "Animals", "Favorite Music Genres"]
    
    # Create rows in order of houses (1 then 2)
    row1 = ["1", house1["Name"], house1["Favorite Book Genres"], house1["Vacation Type"], house1["Animals"], house1["Favorite Music Genres"]]
    row2 = ["2", house2["Name"], house2["Favorite Book Genres"], house2["Vacation Type"], house2["Animals"], house2["Favorite Music Genres"]]
    
    solution = {
        "solution": {
            "header": header,
            "rows": [row1, row2]
        }
    }
    
    # Output the solution as JSON
    print(json.dumps(solution, indent=2))

if __name__ == "__main__":
    main()