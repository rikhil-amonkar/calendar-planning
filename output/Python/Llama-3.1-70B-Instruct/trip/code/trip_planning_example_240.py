import json

def calculate_trip_plan(prague_days, berlin_days, tallinn_days, stockholm_days, conference_window, visit_relatives_window):
    total_days = prague_days + berlin_days + tallinn_days + stockholm_days

    # Calculate the number of days for each city, considering the conference window in Berlin
    berlin_start_day = 6
    berlin_end_day = berlin_start_day + berlin_days - 1
    conference_day = (conference_window[0] + conference_window[1]) // 2

    # Ensure Berlin is visited to attend the conference
    if conference_day < berlin_start_day or conference_day > berlin_end_day:
        raise ValueError("Conference day does not fall within the Berlin visit window")

    # Calculate the day ranges for Prague
    prague_start_day = 1
    prague_end_day = prague_start_day + prague_days - 1

    # Calculate the day ranges for Stockholm
    stockholm_start_day = berlin_end_day + 1
    stockholm_end_day = stockholm_start_day + stockholm_days - 1

    # Calculate the day ranges for Tallinn
    tallinn_start_day = stockholm_end_day + 1
    tallinn_end_day = tallinn_start_day + tallinn_days - 1
    visit_relatives_day = (visit_relatives_window[0] + visit_relatives_window[1]) // 2

    # Ensure Tallinn is visited to visit relatives
    if visit_relatives_day < tallinn_start_day or visit_relatives_day > tallinn_end_day:
        raise ValueError("Visit relatives day does not fall within the Tallinn visit window")

    # Check if the total days add up correctly
    if tallinn_end_day!= total_days:
        raise ValueError("Total days do not add up correctly")

    # Create the trip plan
    trip_plan = [
        {'day_range': f'Day {prague_start_day}-{prague_end_day}', 'place': 'Prague'},
        {'flying': f'Day {prague_end_day}-{prague_end_day}', 'from': 'Prague', 'to': 'Berlin'},
        {'day_range': f'Day {berlin_start_day}-{berlin_end_day}', 'place': 'Berlin'},
        {'flying': f'Day {berlin_end_day}-{berlin_end_day}', 'from': 'Berlin', 'to': 'Stockholm'},
        {'day_range': f'Day {stockholm_start_day}-{stockholm_end_day}', 'place': 'Stockholm'},
        {'flying': f'Day {stockholm_end_day}-{stockholm_end_day}', 'from': 'Stockholm', 'to': 'Tallinn'},
        {'day_range': f'Day {tallinn_start_day}-{tallinn_end_day}', 'place': 'Tallinn'}
    ]

    return trip_plan

def main():
    prague_days = 2
    berlin_days = 3
    tallinn_days = 5
    stockholm_days = 5
    conference_window = (6, 8)
    visit_relatives_window = (8, 12)

    trip_plan = calculate_trip_plan(prague_days, berlin_days, tallinn_days, stockholm_days, conference_window, visit_relatives_window)
    print(json.dumps(trip_plan, indent=4))

if __name__ == "__main__":
    main()