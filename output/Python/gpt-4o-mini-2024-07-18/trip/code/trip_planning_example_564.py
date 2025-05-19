import json

def plan_trip():
    # Define the constraints and durations based on the problem statement
    itinerary = []
    
    # Days allocation
    total_days = 16
    days_istanbul = 2
    days_rome = 3
    days_seville = 4
    days_naples = 7
    days_santorini = 4

    # Days spent in Istanbul (Day 6-7 for relatives)
    itinerary.append({'day_range': 'Day 1-5', 'place': 'Rome'})  # Start in Rome
    itinerary.append({'flying': 'Day 5-5', 'from': 'Rome', 'to': 'Istanbul'})  # Travel to Istanbul
    itinerary.append({'day_range': 'Day 6-7', 'place': 'Istanbul'})  # 2 days in Istanbul
    itinerary.append({'flying': 'Day 7-7', 'from': 'Istanbul', 'to': 'Naples'})  # Travel to Naples
    itinerary.append({'day_range': 'Day 8-14', 'place': 'Naples'})  # 7 days in Naples
    itinerary.append({'flying': 'Day 14-14', 'from': 'Naples', 'to': 'Santorini'})  # Travel to Santorini
    itinerary.append({'day_range': 'Day 15-16', 'place': 'Santorini'})  # 4 days in Santorini (wedding in Day 13-16)
    
    # Output the result as a JSON-formatted string
    return json.dumps(itinerary, indent=2)

# Run the trip planning function
if __name__ == "__main__":
    trip_plan = plan_trip()
    print(trip_plan)