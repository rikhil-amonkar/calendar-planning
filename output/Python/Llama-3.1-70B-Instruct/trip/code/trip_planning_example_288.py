import json

def calculate_trip_plan(stuttgart_days, manchester_days, madrid_days, vienna_days, workshop_window, wedding_window):
    total_days = stuttgart_days + manchester_days + madrid_days + vienna_days

    # Calculate the number of days for each city, considering the workshop window in Stuttgart
    stuttgart_start_day = 11
    stuttgart_end_day = stuttgart_start_day + stuttgart_days - 1
    workshop_day = (workshop_window[0] + workshop_window[1]) // 2

    # Ensure Stuttgart is visited last to attend the workshop
    if workshop_day < stuttgart_start_day or workshop_day > stuttgart_end_day:
        raise ValueError("Workshop day does not fall within the Stuttgart visit window")

    # Calculate the number of days for each city, considering the wedding window in Manchester
    manchester_start_day = 1
    manchester_end_day = manchester_start_day + manchester_days - 1
    wedding_day = (wedding_window[0] + wedding_window[1]) // 2

    # Ensure Manchester is visited first to attend the wedding
    if wedding_day < manchester_start_day or wedding_day > manchester_end_day:
        raise ValueError("Wedding day does not fall within the Manchester visit window")

    # Calculate the day ranges for Madrid
    madrid_start_day = manchester_end_day + 1
    madrid_end_day = madrid_start_day + madrid_days - 1

    # Calculate the day ranges for Vienna
    vienna_start_day = madrid_end_day + 1
    vienna_end_day = vienna_start_day + vienna_days - 1

    # Check if the total days add up correctly
    if vienna_end_day + 1!= stuttgart_start_day:
        raise ValueError("Total days do not add up correctly")

    # Create the trip plan
    trip_plan = [
        {'day_range': f'Day {manchester_start_day}-{manchester_end_day}', 'place': 'Manchester'},
        {'flying': f'Day {manchester_end_day}-{manchester_end_day}', 'from': 'Manchester', 'to': 'Madrid'},
        {'day_range': f'Day {madrid_start_day}-{madrid_end_day}', 'place': 'Madrid'},
        {'flying': f'Day {madrid_end_day}-{madrid_end_day}', 'from': 'Madrid', 'to': 'Vienna'},
        {'day_range': f'Day {vienna_start_day}-{vienna_end_day}', 'place': 'Vienna'},
        {'flying': f'Day {vienna_end_day}-{vienna_end_day}', 'from': 'Vienna', 'to': 'Stuttgart'},
        {'day_range': f'Day {stuttgart_start_day}-{stuttgart_end_day}', 'place': 'Stuttgart'}
    ]

    return trip_plan

def main():
    stuttgart_days = 5
    manchester_days = 7
    madrid_days = 4
    vienna_days = 2
    workshop_window = (11, 15)
    wedding_window = (1, 7)

    trip_plan = calculate_trip_plan(stuttgart_days, manchester_days, madrid_days, vienna_days, workshop_window, wedding_window)
    print(json.dumps(trip_plan, indent=4))

if __name__ == "__main__":
    main()