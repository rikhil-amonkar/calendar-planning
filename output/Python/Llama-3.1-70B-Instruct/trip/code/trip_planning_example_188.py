import json

def calculate_trip_plan(brussels_days, split_days, barcelona_days, conference_window):
    total_days = brussels_days + split_days + barcelona_days

    # Calculate the number of days for each city, considering the conference window in Brussels
    brussels_start_day = 1
    brussels_end_day = brussels_start_day + brussels_days - 1
    conference_day = (conference_window[0] + conference_window[1]) // 2

    # Ensure Brussels is visited first to attend the conference
    if conference_day < brussels_start_day or conference_day > brussels_end_day:
        raise ValueError("Conference day does not fall within the Brussels visit window")

    # Calculate the day ranges for Barcelona
    barcelona_start_day = brussels_end_day + 1
    barcelona_end_day = barcelona_start_day + barcelona_days - 1

    # Calculate the day ranges for Split
    split_start_day = barcelona_end_day + 1
    split_end_day = split_start_day + split_days - 1

    # Check if the total days add up correctly
    if split_end_day!= total_days:
        raise ValueError("Total days do not add up correctly")

    # Create the trip plan
    trip_plan = [
        {'day_range': f'Day {brussels_start_day}-{brussels_end_day}', 'place': 'Brussels'},
        {'flying': f'Day {brussels_end_day}-{brussels_end_day}', 'from': 'Brussels', 'to': 'Barcelona'},
        {'day_range': f'Day {barcelona_start_day}-{barcelona_end_day}', 'place': 'Barcelona'},
        {'flying': f'Day {barcelona_end_day}-{barcelona_end_day}', 'from': 'Barcelona', 'to': 'Split'},
        {'day_range': f'Day {split_start_day}-{split_end_day}', 'place': 'Split'}
    ]

    return trip_plan

def main():
    brussels_days = 2
    split_days = 5
    barcelona_days = 7
    conference_window = (1, 2)

    trip_plan = calculate_trip_plan(brussels_days, split_days, barcelona_days, conference_window)
    print(json.dumps(trip_plan, indent=4))

if __name__ == "__main__":
    main()