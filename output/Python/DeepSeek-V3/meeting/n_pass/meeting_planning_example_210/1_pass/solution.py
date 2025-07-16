import json
from datetime import datetime, timedelta

def parse_time(time_str):
    return datetime.strptime(time_str, "%H:%M")

def format_time(dt):
    return dt.strftime("%-H:%M")

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

    itinerary = []

    # Strategy: Visit Melissa first, then Emily, then Joseph
    # Try to meet Melissa
    travel_time = travel_times[(current_location, melissa_location)]
    arrival_time = current_time + timedelta(minutes=travel_time)
    if arrival_time < melissa_available_end:
        start_time = max(arrival_time, melissa_available_start)
        end_time = start_time + timedelta(minutes=melissa_min_duration)
        if end_time <= melissa_available_end:
            itinerary.append({
                "action": "meet",
                "location": melissa_location,
                "person": "Melissa",
                "start_time": format_time(start_time),
                "end_time": format_time(end_time)
            })
            current_time = end_time
            current_location = melissa_location

            # Try to meet Emily next
            travel_time = travel_times[(current_location, emily_location)]
            arrival_time = current_time + timedelta(minutes=travel_time)
            if arrival_time < emily_available_end:
                start_time = max(arrival_time, emily_available_start)
                end_time = start_time + timedelta(minutes=emily_min_duration)
                if end_time <= emily_available_end:
                    itinerary.append({
                        "action": "meet",
                        "location": emily_location,
                        "person": "Emily",
                        "start_time": format_time(start_time),
                        "end_time": format_time(end_time)
                    })
                    current_time = end_time
                    current_location = emily_location

                    # Try to meet Joseph last
                    travel_time = travel_times[(current_location, joseph_location)]
                    arrival_time = current_time + timedelta(minutes=travel_time)
                    if arrival_time < joseph_available_end:
                        start_time = max(arrival_time, joseph_available_start)
                        end_time = start_time + timedelta(minutes=joseph_min_duration)
                        if end_time <= joseph_available_end:
                            itinerary.append({
                                "action": "meet",
                                "location": joseph_location,
                                "person": "Joseph",
                                "start_time": format_time(start_time),
                                "end_time": format_time(end_time)
                            })

    # If the above schedule didn't work, try alternative orders
    if len(itinerary) < 3:
        itinerary = []
        current_time = parse_time("9:00")
        current_location = "Fisherman's Wharf"

        # Try to meet Joseph first
        travel_time = travel_times[(current_location, joseph_location)]
        arrival_time = current_time + timedelta(minutes=travel_time)
        if arrival_time < joseph_available_end:
            start_time = max(arrival_time, joseph_available_start)
            end_time = start_time + timedelta(minutes=joseph_min_duration)
            if end_time <= joseph_available_end:
                itinerary.append({
                    "action": "meet",
                    "location": joseph_location,
                    "person": "Joseph",
                    "start_time": format_time(start_time),
                    "end_time": format_time(end_time)
                })
                current_time = end_time
                current_location = joseph_location

                # Try to meet Emily next
                travel_time = travel_times[(current_location, emily_location)]
                arrival_time = current_time + timedelta(minutes=travel_time)
                if arrival_time < emily_available_end:
                    start_time = max(arrival_time, emily_available_start)
                    end_time = start_time + timedelta(minutes=emily_min_duration)
                    if end_time <= emily_available_end:
                        itinerary.append({
                            "action": "meet",
                            "location": emily_location,
                            "person": "Emily",
                            "start_time": format_time(start_time),
                            "end_time": format_time(end_time)
                        })
                        current_time = end_time
                        current_location = emily_location

                        # Try to meet Melissa last
                        travel_time = travel_times[(current_location, melissa_location)]
                        arrival_time = current_time + timedelta(minutes=travel_time)
                        if arrival_time < melissa_available_end:
                            start_time = max(arrival_time, melissa_available_start)
                            end_time = start_time + timedelta(minutes=melissa_min_duration)
                            if end_time <= melissa_available_end:
                                itinerary.append({
                                    "action": "meet",
                                    "location": melissa_location,
                                    "person": "Melissa",
                                    "start_time": format_time(start_time),
                                    "end_time": format_time(end_time)
                                })

    # If still not all meetings scheduled, try another order
    if len(itinerary) < 3:
        itinerary = []
        current_time = parse_time("9:00")
        current_location = "Fisherman's Wharf"

        # Try to meet Emily first
        travel_time = travel_times[(current_location, emily_location)]
        arrival_time = current_time + timedelta(minutes=travel_time)
        if arrival_time < emily_available_end:
            start_time = max(arrival_time, emily_available_start)
            end_time = start_time + timedelta(minutes=emily_min_duration)
            if end_time <= emily_available_end:
                itinerary.append({
                    "action": "meet",
                    "location": emily_location,
                    "person": "Emily",
                    "start_time": format_time(start_time),
                    "end_time": format_time(end_time)
                })
                current_time = end_time
                current_location = emily_location

                # Try to meet Joseph next
                travel_time = travel_times[(current_location, joseph_location)]
                arrival_time = current_time + timedelta(minutes=travel_time)
                if arrival_time < joseph_available_end:
                    start_time = max(arrival_time, joseph_available_start)
                    end_time = start_time + timedelta(minutes=joseph_min_duration)
                    if end_time <= joseph_available_end:
                        itinerary.append({
                            "action": "meet",
                            "location": joseph_location,
                            "person": "Joseph",
                            "start_time": format_time(start_time),
                            "end_time": format_time(end_time)
                        })
                        current_time = end_time
                        current_location = joseph_location

                        # Try to meet Melissa last
                        travel_time = travel_times[(current_location, melissa_location)]
                        arrival_time = current_time + timedelta(minutes=travel_time)
                        if arrival_time < melissa_available_end:
                            start_time = max(arrival_time, melissa_available_start)
                            end_time = start_time + timedelta(minutes=melissa_min_duration)
                            if end_time <= melissa_available_end:
                                itinerary.append({
                                    "action": "meet",
                                    "location": melissa_location,
                                    "person": "Melissa",
                                    "start_time": format_time(start_time),
                                    "end_time": format_time(end_time)
                                })

    # Return the best schedule found
    return {"itinerary": itinerary}

if __name__ == "__main__":
    schedule = calculate_schedule()
    print(json.dumps(schedule, indent=2))