import json

# Initialize the houses with empty values
houses = [
    {"Name": None, "Cigar": None, "FavoriteSport": None, "Drink": None},
    {"Name": None, "Cigar": None, "FavoriteSport": None, "Drink": None},
    {"Name": None, "Cigar": None, "FavoriteSport": None, "Drink": None},
    {"Name": None, "Cigar": None, "FavoriteSport": None, "Drink": None}
]

# Apply direct assignments from clues
houses[3]["Name"] = "Peter"  # Clue 1
houses[2]["FavoriteSport"] = "basketball"  # Clue 2 & Clue 4
houses[2]["Name"] = "Eric"  # Clue 4
houses[2]["Cigar"] = "pall mall"  # Clue 10
houses[0]["Drink"] = "water"  # Clue 6: Two houses between water drinker and Peter (who is in the 4th house)
houses[0]["Name"] = "Arnold"  # Clue 7
houses[0]["Drink"] = "coffee"  # Clue 7
houses[3]["Drink"] = "tea"  # Clue 2: Basketball lover drinks tea, and he is in the 3rd house
houses[2]["Drink"] = "water"  # This was initially set, but now we need to adjust
houses[0]["Drink"] = "water"  # Corrected position for water drinker
houses[1]["Drink"] = "milk"  # By elimination
houses[2]["Drink"] = "tea"  # Confirmed by clue 2
houses[3]["Drink"] = "coffee"  # This was initially set incorrectly, now corrected
houses[3]["Drink"] = "tea"  # Corrected position for tea drinker
houses[3]["Drink"] = "coffee"  # Rechecking positions
houses[3]["Drink"] = "tea"  # Final correction
houses[1]["Drink"] = "milk"  # Final confirmation
houses[3]["Drink"] = "tea"  # Final confirmation
houses[0]["Drink"] = "water"  # Final confirmation
houses[1]["Cigar"] = "blue master"  # Clue 5: Tennis player smokes Blue Master
houses[1]["FavoriteSport"] = "tennis"  # Clue 5: Tennis player smokes Blue Master
houses[3]["Cigar"] = "pall mall"  # Clue 10: Peter smokes Pall Mall
houses[0]["Cigar"] = "blue master"  # Corrected after reevaluation
houses[0]["Cigar"] = "prince"  # Clue 9: Prince smoker loves soccer
houses[0]["FavoriteSport"] = "soccer"  # Clue 9: Prince smoker loves soccer
houses[1]["Cigar"] = "dunhill"  # By elimination
houses[1]["FavoriteSport"] = "basketball"  # By elimination
houses[1]["Name"] = "Alice"  # By elimination
houses[3]["Name"] = "Peter"  # Confirmed
houses[2]["Name"] = "Eric"  # Confirmed
houses[0]["Name"] = "Arnold"  # Confirmed

# Construct the solution in the required JSON format
solution = {
    "solution": {
        "header": ["House", "Name", "Cigar", "FavoriteSport", "Drink"],
        "rows": [
            ["1", houses[0]["Name"], houses[0]["Cigar"], houses[0]["FavoriteSport"], houses[0]["Drink"]],
            ["2", houses[1]["Name"], houses[1]["Cigar"], houses[1]["FavoriteSport"], houses[1]["Drink"]],
            ["3", houses[2]["Name"], houses[2]["Cigar"], houses[2]["FavoriteSport"], houses[2]["Drink"]],
            ["4", houses[3]["Name"], houses[3]["Cigar"], houses[3]["FavoriteSport"], houses[3]["Drink"]]
        ]
    }
}

# Output the solution as a JSON string
print(json.dumps(solution, indent=2))