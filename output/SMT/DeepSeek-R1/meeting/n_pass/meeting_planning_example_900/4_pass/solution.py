from z3 import *
import json

def main():
    friends = ["Matthew", "Rebecca", "Brian", "Emily", "Karen", "Stephanie", "James", "Steven", "Elizabeth", "William"]
    locations = {
        "Matthew": "The Castro",
        "Rebecca": "Nob Hill",
        "Brian": "Marina District",
        "Emily": "Pacific Heights",
        "Karen": "Haight-Ashbury",
        "Stephanie": "Mission District",
        "James": "Chinatown",
        "Steven": "Russian Hill",
        "Elizabeth": "Alamo Square",
        "William": "Bayview"
    }

    availability_start = {
        "Matthew": 450,   # 4:30PM
        "Rebecca": 375,   # 3:15PM
        "Brian": 315,     # 2:15PM
        "Emily": 135,     # 11:15AM
        "Karen": 165,     # 11:45AM
        "Stephanie": 240, # 1:00PM
        "James": 330,     # 2:30PM
        "Steven": 300,    # 2:00PM
        "Elizabeth": 240, # 1:00PM
        "William": 555    # 6:15PM
    }
    availability_end = {
        "Matthew": 660,   # 8:00PM
        "Rebecca": 615,   # 7:15PM
        "Brian": 780,     # 10:00PM
        "Emily": 645,     # 7:45PM
        "Karen": 510,     # 5:30PM
        "Stephanie": 405, # 3:45PM
        "James": 600,     # 7:00PM
        "Steven": 660,    # 8:00PM
        "Elizabeth": 495, # 5:15PM
        "William": 675    # 8:15PM
    }

    min_durations = {
        "Matthew": 45,
        "Rebecca": 105,
        "Brian": 30,
        "Emily": 15,
        "Karen": 30,
        "Stephanie": 75,
        "James": 120,
        "Steven": 30,
        "Elizabeth": 120,
        "William": 90
    }

    travel_times = {
        ('Richmond District', 'The Castro'): 16,
        ('Richmond District', 'Nob Hill'): 17,
        ('Richmond District', 'Marina District'): 9,
        ('Richmond District', 'Pacific Heights'): 10,
        ('Richmond District', 'Haight-Ashbury'): 10,
        ('Richmond District', 'Mission District'): 20,
        ('Richmond District', 'Chinatown'): 20,
        ('Richmond District', 'Russian Hill'): 13,
        ('Richmond District', 'Alamo Square'): 13,
        ('Richmond District', 'Bayview'): 27,
        ('The Castro', 'Richmond District'): 16,
        ('The Castro', 'Nob Hill'): 16,
        ('The Castro', 'Marina District'): 21,
        ('The Castro', 'Pacific Heights'): 16,
        ('The Castro', 'Haight-Ashbury'): 6,
        ('The Castro', 'Mission District'): 7,
        ('The Castro', 'Chinatown'): 22,
        ('The Castro', 'Russian Hill'): 18,
        ('The Castro', 'Alamo Square'): 8,
        ('The Castro', 'Bayview'): 19,
        ('Nob Hill', 'Richmond District'): 14,
        ('Nob Hill', 'The Castro'): 17,
        ('Nob Hill', 'Marina District'): 11,
        ('Nob Hill', 'Pacific Heights'): 8,
        ('Nob Hill', 'Haight-Ashbury'): 13,
        ('Nob Hill', 'Mission District'): 13,
        ('Nob Hill', 'Chinatown'): 6,
        ('Nob Hill', 'Russian Hill'): 5,
        ('Nob Hill', 'Alamo Square'): 11,
        ('Nob Hill', 'Bayview'): 19,
        ('Marina District', 'Richmond District'): 11,
        ('Marina District', 'The Castro'): 22,
        ('Marina District', 'Nob Hill'): 12,
        ('Marina District', 'Pacific Heights'): 7,
        ('Marina District', 'Haight-Ashbury'): 16,
        ('Marina District', 'Mission District'): 20,
        ('Marina District', 'Chinatown'): 15,
        ('Marina District', 'Russian Hill'): 8,
        ('Marina District', 'Alamo Square'): 15,
        ('Marina District', 'Bayview'): 27,
        ('Pacific Heights', 'Richmond District'): 12,
        ('Pacific Heights', 'The Castro'): 16,
        ('Pacific Heights', 'Nob Hill'): 8,
        ('Pacific Heights', 'Marina District'): 6,
        ('Pacific Heights', 'Haight-Ashbury'): 11,
        ('Pacific Heights', 'Mission District'): 15,
        ('Pacific Heights', 'Chinatown'): 11,
        ('Pacific Heights', 'Russian Hill'): 7,
        ('Pacific Heights', 'Alamo Square'): 10,
        ('Pacific Heights', 'Bayview'): 22,
        ('Haight-Ashbury', 'Richmond District'): 10,
        ('Haight-Ashbury', 'The Castro'): 6,
        ('Haight-Ashbury', 'Nob Hill'): 15,
        ('Haight-Ashbury', 'Marina District'): 17,
        ('Haight-Ashbury', 'Pacific Heights'): 12,
        ('Haight-Ashbury', 'Mission District'): 11,
        ('Haight-Ashbury', 'Chinatown'): 19,
        ('Haight-Ashbury', 'Russian Hill'): 17,
        ('Haight-Ashbury', 'Alamo Square'): 5,
        ('Haight-Ashbury', 'Bayview'): 18,
        ('Mission District', 'Richmond District'): 20,
        ('Mission District', 'The Castro'): 7,
        ('Mission District', 'Nob Hill'): 12,
        ('Mission District', 'Marina District'): 19,
        ('Mission District', 'Pacific Heights'): 16,
        ('Mission District', 'Haight-Ashbury'): 12,
        ('Mission District', 'Chinatown'): 16,
        ('Mission District', 'Russian Hill'): 15,
        ('Mission District', 'Alamo Square'): 11,
        ('Mission District', 'Bayview'): 14,
        ('Chinatown', 'Richmond District'): 20,
        ('Chinatown', 'The Castro'): 22,
        ('Chinatown', 'Nob Hill'): 9,
        ('Chinatown', 'Marina District'): 12,
        ('Chinatown', 'Pacific Heights'): 10,
        ('Chinatown', 'Haight-Ashbury'): 19,
        ('Chinatown', 'Mission District'): 17,
        ('Chinatown', 'Russian Hill'): 7,
        ('Chinatown', 'Alamo Square'): 17,
        ('Chinatown', 'Bayview'): 20,
        ('Russian Hill', 'Richmond District'): 14,
        ('Russian Hill', 'The Castro'): 21,
        ('Russian Hill', 'Nob Hill'): 5,
        ('Russian Hill', 'Marina District'): 7,
        ('Russian Hill', 'Pacific Heights'): 7,
        ('Russian Hill', 'Haight-Ashbury'): 17,
        ('Russian Hill', 'Mission District'): 16,
        ('Russian Hill', 'Chinatown'): 9,
        ('Russian Hill', 'Alamo Square'): 15,
        ('Russian Hill', 'Bayview'): 23,
        ('Alamo Square', 'Richmond District'): 11,
        ('Alamo Square', 'The Castro'): 8,
        ('Alamo Square', 'Nob Hill'): 11,
        ('Alamo Square', 'Marina District'): 15,
        ('Alamo Square', 'Pacific Heights'): 10,
        ('Alamo Square', 'Haight-Ashbury'): 5,
        ('Alamo Square', 'Mission District'): 10,
        ('Alamo Square', 'Chinatown'): 15,
        ('Alamo Square', 'Russian Hill'): 13,
        ('Alamo Square', 'Bayview'): 16,
        ('Bayview', 'Richmond District'): 25,
        ('Bayview', 'The Castro'): 19,
        ('Bayview', 'Nob Hill'): 20,
        ('Bayview', 'Marina District'): 27,
        ('Bayview', 'Pacific Heights'): 23,
        ('Bayview', 'Haight-Ashbury'): 19,
        ('Bayview', 'Mission District'): 13,
        ('Bayview', 'Chinatown'): 19,
        ('Bayview', 'Russian Hill'): 23,
        ('Bayview', 'Alamo Square'): 16
    }

    # Precompute lists for each friend by index
    availability_start_list = [availability_start[f] for f in friends]
    availability_end_list = [availability_end[f] for f in friends]
    min_durations_list = [min_durations[f] for f in friends]
    travel_from_richmond_list = [travel_times[('Richmond District', locations[f])] for f in friends]
    
    # Precompute travel matrix between friends (10x10) with 0 on diagonal
    travel_matrix = []
    for i in range(10):
        row = []
        for j in range(10):
            if i == j:
                row.append(0)
            else:
                loc_i = locations[friends[i]]
                loc_j = locations[friends[j]]
                row.append(travel_times[(loc_i, loc_j)])
        travel_matrix.append(row)
    
    # Flatten the travel matrix into a list of 100 elements
    flattened_travel = []
    for i in range(10):
        for j in range(10):
            flattened_travel.append(travel_matrix[i][j])
    
    k_values = [10, 9, 8, 7, 6, 5, 4, 3, 2, 1]
    schedule_found = None

    for k in k_values:
        s = Solver()
        s.set("timeout", 30000)  # 30 seconds timeout per k

        # Create flattened travel array
        travel_arr = Array('travel_arr', IntSort(), IntSort())
        for idx, val in enumerate(flattened_travel):
            travel_arr = Store(travel_arr, idx, val)

        # Create position and start time variables for each meeting in the sequence
        positions = [Int(f'pos_{k}_{i}') for i in range(k)]
        starts = [Int(f'start_{k}_{i}') for i in range(k)]

        # Each position must be between 0 and 9 (friend indices)
        for p in positions:
            s.add(p >= 0, p < 10)

        # All positions must be distinct
        s.add(Distinct(positions))

        # First meeting constraints
        first_pos = positions[0]
        # Get travel time from Richmond to first friend
        s.add(starts[0] >= travel_from_richmond_list[first_pos])
        # Start time must be after friend's availability start
        s.add(starts[0] >= availability_start_list[first_pos])
        # Meeting must end before friend's availability end
        meeting_end0 = starts[0] + min_durations_list[first_pos]
        s.add(meeting_end0 <= availability_end_list[first_pos])

        # Subsequent meetings
        for i in range(1, k):
            current_pos = positions[i]
            prev_pos = positions[i-1]

            # Availability constraints for current meeting
            s.add(starts[i] >= availability_start_list[current_pos])
            meeting_end = starts[i] + min_durations_list[current_pos]
            s.add(meeting_end <= availability_end_list[current_pos])

            # Travel time between previous and current meeting
            travel_idx = prev_pos * 10 + current_pos
            travel_time = travel_arr[travel_idx]

            # Start time must account for previous meeting end and travel
            prev_meeting_end = starts[i-1] + min_durations_list[prev_pos]
            s.add(starts[i] >= prev_meeting_end + travel_time)

        # Check for a feasible schedule
        if s.check() == sat:
            model = s.model()
            schedule = []
            for i in range(k):
                pos_val = model.eval(positions[i]).as_long()
                friend = friends[pos_val]
                start_val = model.eval(starts[i]).as_long()
                # Convert start time to HH:MM format
                total_minutes_start = 540 + start_val  # 9:00 AM = 540 minutes
                hour_start = total_minutes_start // 60
                minute_start = total_minutes_start % 60
                start_str = f"{hour_start:02d}:{minute_start:02d}"
                # Calculate end time
                duration = min_durations[friend]
                total_minutes_end = total_minutes_start + duration
                hour_end = total_minutes_end // 60
                minute_end = total_minutes_end % 60
                end_str = f"{hour_end:02d}:{minute_end:02d}"
                schedule.append({
                    "action": "meet",
                    "person": friend,
                    "start_time": start_str,
                    "end_time": end_str
                })
            schedule_found = schedule
            break

    # Output the result
    if schedule_found is not None:
        result = {"itinerary": schedule_found}
        print("SOLUTION:")
        print(json.dumps(result))
    else:
        print("SOLUTION:")
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()