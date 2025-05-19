import json

def calculate_trip_plan(split_days, santorini_days, london_days, conference_window):
    total_days = split_days + santorini_days + london_days

    # Calculate the number of days for each city, considering the conference window in Santorini
    santorini_start_day = 12
    santorini_end_day = santorini_start_day + santorini_days - 1
    conference_day = (conference_window[0] + conference_window[1]) // 2

    # Ensure Santorini is visited to attend the conference
    if conference_day < santorini_start_day or conference_day > santorini_end_day:
        raise ValueError("Conference day does not fall within the Santorini visit window")

    # Calculate the day ranges for Split
    split_start_day = 1
    split_end_day = split_start_day + split_days - 1

    # Calculate the day ranges for London
    london_start_day = split_end_day + 1
    london_end_day = london_start_day + london_days - 1

    # Check if the total days add up correctly
    if london_end_day!= total_days:
        raise ValueError("Total days do not add up correctly")

    # Create the trip plan
    trip_plan = [
        {'day_range': f'Day {split_start_day}-{split_end_day}', 'place': 'Split'},
        {'flying': f'Day {split_end_day}-{split_end_day}', 'from': 'Split', 'to': 'London'},
        {'day_range': f'Day {london_start_day}-{london_start_day}', 'place': 'London'},
        {'flying': f'Day {london_start_day}-{london_start_day}', 'from': 'London', 'to': 'Santorini'},
        {'day_range': f'Day {santorini_start_day}-{santorini_end_day}', 'place': 'Santorini'},
        {'flying': f'Day {santorini_end_day}-{santorini_end_day}', 'from': 'Santorini', 'to': 'London'},
        {'day_range': f'Day {santorini_end_day+1}-{total_days}', 'place': 'London'}
    ]

    return trip_plan

def main():
    split_days = 6
    santorini_days = 7
    london_days = 7
    conference_window = (12, 18)

    trip_plan = calculate_trip_plan(split_days, santorini_days, london_days, conference_window)
    print(json.dumps(trip_plan, indent=4))

if __name__ == "__main__":
    main()