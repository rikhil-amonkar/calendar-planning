import json

def main():
    # Convert time to minutes past 9:00 AM (0 minutes = 9:00)
    def time_to_minutes(time_str):
        parts = time_str.split(':')
        hour = int(parts[0])
        minute = int(parts[1]) if len(parts) > 1 else 0
        return (hour - 9) * 60 + minute

    def minutes_to_time(minutes):
        total_minutes = minutes
        hours = total_minutes // 60
        mins = total_minutes % 60
        return f"{9 + hours}:{mins:02d}"

    # Travel times dictionary
    travel_times = {
        ('Bayview', 'Union Square'): 17,
        ('Bayview', 'Presidio'): 31,
        ('Union Square', 'Bayview'): 15,
        ('Union Square', 'Presidio'): 24,
        ('Presidio', 'Bayview'): 31,
        ('Presidio', 'Union Square'): 22
    }

    # Constraints
    richard_available_start = time_to_minutes('8:45')  # -15 minutes from 9:00
    richard_available_end = time_to_minutes('13:00')   # 240 minutes
    charles_available_start = time_to_minutes('9:45')  # 45 minutes
    charles_available_end = time_to_minutes('13:00')   # 240 minutes

    min_richard = 120
    min_charles = 120

    # Possible schedules: Richard first or Charles first
    best_schedule = None
    best_metric = (-1, -1)  # (num_met_desired, total_meeting_time)

    # Option 1: Richard then Charles
    arrive_richard = travel_times[('Bayview', 'Union Square')]  # 17
    start_richard = max(arrive_richard, richard_available_start)
    end_richard = start_richard + min_richard
    if end_richard > richard_available_end:
        end_richard = richard_available_end
    actual_richard_duration = end_richard - start_richard

    travel_to_charles = travel_times[('Union Square', 'Presidio')]  # 24
    arrive_charles = end_richard + travel_to_charles
    start_charles = max(arrive_charles, charles_available_start)
    end_charles = min(charles_available_end, charles_available_end)  # Meet until Charles ends
    actual_charles_duration = end_charles - start_charles

    num_desired_met = 0
    if actual_richard_duration >= min_richard:
        num_desired_met += 1
    if actual_charles_duration >= min_charles:
        num_desired_met += 1
    total_time = actual_richard_duration + actual_charles_duration

    option1_metric = (num_desired_met, total_time)
    if option1_metric > best_metric:
        best_metric = option1_metric
        best_schedule = [
            {'action': 'meet', 'location': 'Union Square', 'person': 'Richard', 
             'start_time': minutes_to_time(start_richard), 'end_time': minutes_to_time(end_richard)},
            {'action': 'meet', 'location': 'Presidio', 'person': 'Charles', 
             'start_time': minutes_to_time(start_charles), 'end_time': minutes_to_time(end_charles)}
        ]

    # Option 2: Charles then Richard
    arrive_charles = travel_times[('Bayview', 'Presidio')]  # 31
    start_charles = max(arrive_charles, charles_available_start)  # 45
    end_charles = start_charles + min_charles
    if end_charles > charles_available_end:
        end_charles = charles_available_end
    actual_charles_duration = end_charles - start_charles

    travel_to_richard = travel_times[('Presidio', 'Union Square')]  # 22
    arrive_richard = end_charles + travel_to_richard
    start_richard = max(arrive_richard, richard_available_start)
    end_richard = min(richard_available_end, richard_available_end)
    actual_richard_duration = end_richard - start_richard

    num_desired_met = 0
    if actual_charles_duration >= min_charles:
        num_desired_met += 1
    if actual_richard_duration >= min_richard:
        num_desired_met += 1
    total_time = actual_charles_duration + actual_richard_duration

    option2_metric = (num_desired_met, total_time)
    if option2_metric > best_metric:
        best_metric = option2_metric
        best_schedule = [
            {'action': 'meet', 'location': 'Presidio', 'person': 'Charles', 
             'start_time': minutes_to_time(start_charles), 'end_time': minutes_to_time(end_charles)},
            {'action': 'meet', 'location': 'Union Square', 'person': 'Richard', 
             'start_time': minutes_to_time(start_richard), 'end_time': minutes_to_time(end_richard)}
        ]

    # Output the best schedule as JSON
    result = {'itinerary': best_schedule}
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()