import json

def generate_itinerary():
    # Define the constraints
    london_days = 2
    santorini_days = 6
    istanbul_days = 3
    total_days = 10
    conference_days = [5, 10]

    # Initialize the itinerary
    itinerary = []

    # Day 1-2: London
    itinerary.append({"day_range": f"Day 1-{london_days}", "place": "London"})

    # Day 2-7: Santorini
    start_day_santorini = london_days
    end_day_santorini = start_day_santorini + santorini_days - 1
    itinerary.append({"day_range": f"Day {start_day_santorini}-{end_day_santorini}", "place": "Santorini"})

    # Day 7-9: Istanbul
    start_day_istanbul = end_day_santorini - 1
    end_day_istanbul = start_day_istanbul + istanbul_days - 1
    itinerary.append({"day_range": f"Day {start_day_istanbul}-{end_day_istanbul}", "place": "Istanbul"})

    # Day 9-10: Santorini
    start_day_final_santorini = end_day_istanbul - 1
    end_day_final_santorini = total_days
    itinerary.append({"day_range": f"Day {start_day_final_santorini}-{end_day_final_santorini}", "place": "Santorini"})

    # Output the itinerary as JSON
    return json.dumps({"itinerary": itinerary}, indent=4)

# Generate and print the itinerary
print(generate_itinerary())