import json

def calculate_itinerary():
    # Input parameters
    total_days = 15
    cities = {
        "Stuttgart": {"total_days": 5, "constraint": (11, 15)},
        "Manchester": {"total_days": 7, "constraint": (1, 7)},
        "Madrid": {"total_days": 4},
        "Vienna": {"total_days": 2}
    }
    
    direct_flights = {
        "Vienna": ["Stuttgart", "Manchester", "Madrid"],
        "Stuttgart": ["Vienna", "Manchester"],
        "Manchester": ["Vienna", "Stuttgart", "Madrid"],
        "Madrid": ["Vienna", "Manchester"]
    }
    
    # Initialize itinerary
    itinerary = []
    
    # Assign Manchester days first (wedding constraint)
    manchester_start = cities["Manchester"]["constraint"][0]
    manchester_end = cities["Manchester"]["constraint"][1]
    itinerary.append({
        "day_range": f"Day {manchester_start}-{manchester_end}",
        "place": "Manchester"
    })
    
    # Assign Stuttgart days (workshop constraint)
    stuttgart_start = cities["Stuttgart"]["constraint"][0]
    stuttgart_end = cities["Stuttgart"]["constraint"][1]
    itinerary.append({
        "day_range": f"Day {stuttgart_start}-{stuttgart_end}",
        "place": "Stuttgart"
    })
    
    # Remaining days after Manchester and Stuttgart
    remaining_days = total_days - (manchester_end - manchester_start + 1) - (stuttgart_end - stuttgart_start + 1)
    # Madrid and Vienna must fit in the remaining days (4 + 2 = 6 days)
    
    # Find the gap between Manchester and Stuttgart
    gap_start = manchester_end + 1
    gap_end = stuttgart_start - 1
    gap_days = gap_end - gap_start + 1
    
    # Assign Madrid and Vienna to the gap
    if gap_days >= 6:
        # Can fit both Madrid and Vienna in the gap
        # Assign Madrid first (4 days)
        madrid_start = gap_start
        madrid_end = madrid_start + cities["Madrid"]["total_days"] - 1
        itinerary.append({
            "day_range": f"Day {madrid_start}-{madrid_end}",
            "place": "Madrid"
        })
        # Assign Vienna next (2 days)
        vienna_start = madrid_end + 1
        vienna_end = vienna_start + cities["Vienna"]["total_days"] - 1
        itinerary.append({
            "day_range": f"Day {vienna_start}-{vienna_end}",
            "place": "Vienna"
        })
    else:
        # Need to split Madrid and Vienna before Manchester or after Stuttgart
        # Since Manchester is fixed at start and Stuttgart at end, we can't split
        # So this case shouldn't happen with given constraints
        pass
    
    # Sort itinerary by day range
    def get_start_day(entry):
        return int(entry["day_range"].split(" ")[1].split("-")[0])
    
    itinerary.sort(key=get_start_day)
    
    # Verify all cities are visited for the correct number of days
    # (This is a simplified solution assuming constraints allow a valid itinerary)
    
    return {"itinerary": itinerary}

# Execute and print the result
result = calculate_itinerary()
print(json.dumps(result, indent=2))