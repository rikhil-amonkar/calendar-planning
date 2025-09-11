import json

def main():
    # Convert time string to minutes since midnight
    def time_to_minutes(time_str):
        parts = time_str.split(':')
        hours = int(parts[0])
        minutes = int(parts[1]) if len(parts) > 1 else 0
        return hours * 60 + minutes

    # Convert minutes since midnight to time string
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"

    # Define travel times between locations
    travel_times = {
        ('Financial District', 'Chinatown'): 5,
        ('Financial District', 'Golden Gate Park'): 23,
        ('Chinatown', 'Financial District'): 5,
        ('Chinatown', 'Golden Gate Park'): 23,
        ('Golden Gate Park', 'Financial District'): 26,
        ('Golden Gate Park', 'Chinatown'): 23
    }

    # Define constraints
    start_time = time_to_minutes("9:00")  # Start at Financial District
    kenneth_available_start = time_to_minutes("12:00")
    kenneth_available_end = time_to_minutes("15:00")
    kenneth_min_duration = 90
    barbara_available_start = time_to_minutes("8:15")
    barbara_available_end = time_to_minutes("19:00")
    barbara_min_duration = 45

    # Define the two possible meeting orders
    orders = [
        ['Golden Gate Park', 'Chinatown'],  # Meet Barbara first, then Kenneth
        ['Chinatown', 'Golden Gate Park']   # Meet Kenneth first, then Barbara
    ]

    best_schedule = None
    best_total_meeting_time = -1

    for order in orders:
        current_time = start_time
        meetings = []
        valid = True
        total_meeting_time = 0

        # First meeting
        loc1 = order[0]
        travel_time_to_loc1 = travel_times[('Financial District', loc1)]
        arrival_loc1 = current_time + travel_time_to_loc1

        if loc1 == 'Golden Gate Park':
            # Meeting Barbara
            meeting_start = max(arrival_loc1, barbara_available_start)
            # Calculate latest departure time to meet Kenneth
            travel_to_kenneth = travel_times[('Golden Gate Park', 'Chinatown')]
            latest_departure = kenneth_available_end - kenneth_min_duration - travel_to_kenneth
            meeting_end = min(latest_departure, barbara_available_end)
            meeting_duration = meeting_end - meeting_start
            if meeting_duration < barbara_min_duration:
                valid = False
            else:
                meetings.append(('meet', 'Golden Gate Park', 'Barbara', meeting_start, meeting_end))
                total_meeting_time += meeting_duration
                current_time = meeting_end + travel_to_kenneth
        else:  # Chinatown
            # Meeting Kenneth
            meeting_start = max(arrival_loc1, kenneth_available_start)
            meeting_end = meeting_start + kenneth_min_duration
            if meeting_end > kenneth_available_end:
                valid = False
            else:
                meetings.append(('meet', 'Chinatown', 'Kenneth', meeting_start, meeting_end))
                total_meeting_time += kenneth_min_duration
                current_time = meeting_end

        if not valid:
            continue

        # Second meeting
        loc2 = order[1]
        travel_time_to_loc2 = travel_times[(loc1, loc2)]
        arrival_loc2 = current_time  # Already included travel time in current_time update

        if loc2 == 'Golden Gate Park':
            # Meeting Barbara
            meeting_start = max(arrival_loc2, barbara_available_start)
            meeting_end = meeting_start + barbara_min_duration
            if meeting_end > barbara_available_end:
                valid = False
            else:
                meetings.append(('meet', 'Golden Gate Park', 'Barbara', meeting_start, meeting_end))
                total_meeting_time += barbara_min_duration
        else:  # Chinatown
            # Meeting Kenneth
            meeting_start = max(arrival_loc2, kenneth_available_start)
            meeting_end = meeting_start + kenneth_min_duration
            if meeting_end > kenneth_available_end:
                valid = False
            else:
                meetings.append(('meet', 'Chinatown', 'Kenneth', meeting_start, meeting_end))
                total_meeting_time += kenneth_min_duration

        if valid and total_meeting_time > best_total_meeting_time:
            best_total_meeting_time = total_meeting_time
            best_schedule = meetings

    # Format the best schedule as JSON
    itinerary = []
    for meeting in best_schedule:
        action, location, person, start, end = meeting
        itinerary.append({
            "action": action,
            "location": location,
            "person": person,
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(end)
        })

    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()