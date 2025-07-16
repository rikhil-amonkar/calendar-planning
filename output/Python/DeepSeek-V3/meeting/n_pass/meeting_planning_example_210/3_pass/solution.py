import json
from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(dt):
    return dt.strftime("%H:%M")

def calculate_schedule():
    # Input parameters
    travel_times = {
        ('Fisherman\'s Wharf', 'Presidio'): 17,
        ('Fisherman\'s Wharf', 'Richmond District'): 18,
        ('Fisherman\'s Wharf', 'Financial District'): 11,
        ('Presidio', 'Fisherman\'s Wharf'): 19,
        ('Presidio', 'Richmond District'): 7,
        ('Presidio', 'Financial District'): 23,
        ('Richmond District', 'Fisherman\'s Wharf'): 18,
        ('Richmond District', 'Presidio'): 7,
        ('Richmond District', 'Financial District'): 22,
        ('Financial District', 'Fisherman\'s Wharf'): 10,
        ('Financial District', 'Presidio'): 22,
        ('Financial District', 'Richmond District'): 21,
    }

    # Constraints
    current_time = parse_time("9:00")
    current_location = "Fisherman's Wharf"

    emily_available_start = parse_time("16:15")
    emily_available_end = parse_time("21:00")
    emily_min_duration = 105  # minutes
    emily_location = "Presidio"

    joseph_available_start = parse_time("17:15")
    joseph_available_end = parse_time("22:00")
    joseph_min_duration = 120  # minutes
    joseph_location = "Richmond District"

    melissa_available_start = parse_time("15:45")
    melissa_available_end = parse_time("21:45")
    melissa_min_duration = 75  # minutes
    melissa_location = "Financial District"

    def try_schedule(order):
        nonlocal current_time, current_location
        temp_time = current_time
        temp_location = current_location
        temp_itinerary = []
        
        for person in order:
            if person == "Emily":
                available_start = emily_available_start
                available_end = emily_available_end
                min_duration = emily_min_duration
                location = emily_location
            elif person == "Joseph":
                available_start = joseph_available_start
                available_end = joseph_available_end
                min_duration = joseph_min_duration
                location = joseph_location
            elif person == "Melissa":
                available_start = melissa_available_start
                available_end = melissa_available_end
                min_duration = melissa_min_duration
                location = melissa_location
            
            travel_time = travel_times[(temp_location, location)]
            arrival_time = temp_time + timedelta(minutes=travel_time)
            
            # Calculate earliest possible start time
            start_time = max(arrival_time, available_start)
            end_time = start_time + timedelta(minutes=min_duration)
            
            if end_time > available_end:
                return None  # Can't schedule this meeting
            
            temp_itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": format_time(start_time),
                "end_time": format_time(end_time)
            })
            temp_time = end_time
            temp_location = location
        
        return temp_itinerary

    # Try all possible meeting orders to find the optimal schedule
    possible_orders = [
        ["Melissa", "Emily", "Joseph"],  # Original order
        ["Melissa", "Joseph", "Emily"],
        ["Emily", "Melissa", "Joseph"],
        ["Emily", "Joseph", "Melissa"],
        ["Joseph", "Melissa", "Emily"],
        ["Joseph", "Emily", "Melissa"]
    ]

    best_itinerary = []
    
    for order in possible_orders:
        current_time = parse_time("9:00")
        current_location = "Fisherman's Wharf"
        itinerary = try_schedule(order)
        if itinerary and len(itinerary) == 3:
            # Check if this schedule is better (earlier finish time)
            if not best_itinerary or parse_time(itinerary[-1]['end_time']) < parse_time(best_itinerary[-1]['end_time']):
                best_itinerary = itinerary

    return {"itinerary": best_itinerary}

if __name__ == "__main__":
    schedule = calculate_schedule()
    print(json.dumps(schedule, indent=2))