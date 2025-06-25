import json

def main():
    # Input constraints
    total_days = 14
    city_days = {
        "Split": 5,
        "Vilnius": 4,
        "Santorini": 2,
        "Madrid": 6
    }
    fixed_events = {
        "Santorini": (13, 14)   # Fixed days for Santorini
    }
    # Known sequence from the flight connections
    sequence = ["Vilnius", "Split", "Madrid", "Santorini"]
    
    # Initialize the blocks for each city
    blocks = []
    
    # Start with the fixed Santorini block
    santorini_block = fixed_events["Santorini"]
    blocks.append(santorini_block)
    
    # Work backwards to compute blocks for Madrid, Split, Vilnius
    prev_start = santorini_block[0]  # Start day of Santorini
    for city in reversed(sequence[:-1]):  # Exclude Santorini and reverse
        end_day = prev_start
        num_days = city_days[city]
        start_day = end_day - (num_days - 1)
        blocks.insert(0, (start_day, end_day))
        prev_start = start_day
    
    # Build the itinerary list
    itinerary_list = []
    for i in range(len(sequence)):
        start, end = blocks[i]
        if start == end:
            day_range_str = f"Day {start}"
        else:
            day_range_str = f"Day {start}-{end}"
        itinerary_list.append({
            "day_range": day_range_str,
            "place": sequence[i]
        })
    
    # Create the result dictionary
    result = {"itinerary": itinerary_list}
    
    # Output as JSON
    print(json.dumps(result))

if __name__ == "__main__":
    main()