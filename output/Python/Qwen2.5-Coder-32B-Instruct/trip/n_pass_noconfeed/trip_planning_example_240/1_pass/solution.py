import json

def calculate_itinerary():
    # Define the constraints
    total_days = 12
    prague_stay = 2
    berlin_stay = 3
    tallinn_stay = 5
    stockholm_stay = 5
    berlin_conference_days = [6, 8]
    tallinn_relative_visit_days = range(8, 13)
    
    # Initialize the itinerary
    itinerary = []
    
    # Start in Prague for 2 days (Day 1-2)
    itinerary.append({"day_range": f"Day 1-{prague_stay}", "place": "Prague"})
    
    # Move to Tallinn for 2 days (Day 3-4) to connect to Berlin for the conference
    itinerary.append({"day_range": f"Day {prague_stay+1}-{prague_stay+2}", "place": "Tallinn"})
    
    # Attend conference in Berlin (Day 5-8)
    berlin_start_day = prague_stay + 2
    berlin_end_day = berlin_start_day + berlin_stay - 1
    itinerary.append({"day_range": f"Day {berlin_start_day}-{berlin_end_day}", "place": "Berlin"})
    
    # Stay in Tallinn for 3 more days (Day 8-10) to visit relatives
    tallinn_start_day = berlin_end_day
    tallinn_end_day = tallinn_start_day + (tallinn_stay - 2)
    itinerary.append({"day_range": f"Day {tallinn_start_day}-{tallinn_end_day}", "place": "Tallinn"})
    
    # Move to Stockholm for 5 days (Day 11-15)
    stockholm_start_day = tallinn_end_day
    stockholm_end_day = stockholm_start_day + stockholm_stay - 1
    itinerary.append({"day_range": f"Day {stockholm_start_day}-{stockholm_end_day}", "place": "Stockholm"})
    
    # Output the itinerary as JSON
    return json.dumps({"itinerary": itinerary})

# Run the function and print the result
print(calculate_itinerary())