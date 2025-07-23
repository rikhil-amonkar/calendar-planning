from z3 import *

def main():
    # Locations
    locations = ['H', 'B', 'C', 'W', 'BV', 'F', 'A']
    
    # Travel times dictionary
    travel_time_dict = {
        ('H', 'B'): 15, ('H', 'C'): 20, ('H', 'W'): 25, ('H', 'BV'): 35, ('H', 'F'): 25, ('H', 'A'): 20,
        ('B', 'H'): 15, ('B', 'C'): 10, ('B', 'W'): 20, ('B', 'BV'): 25, ('B', 'F'): 30, ('B', 'A'): 35,
        ('C', 'H'): 20, ('C', 'B'): 10, ('C', 'W'): 15, ('C', 'BV'): 30, ('C', 'F'): 25, ('C', 'A'): 30,
        ('W', 'H'): 25, ('W', 'B'): 20, ('W', 'C'): 15, ('W', 'BV'): 15, ('W', 'F'): 30, ('W', 'A'): 35,
        ('BV', 'H'): 35, ('BV', 'B'): 25, ('BV', 'C'): 30, ('BV', 'W'): 15, ('BV', 'F'): 20, ('BV', 'A'): 15,
        ('F', 'H'): 25, ('F', 'B'): 30, ('F', 'C'): 25, ('F', 'W'): 30, ('F', 'BV'): 20, ('F', 'A'): 10,
        ('A', 'H'): 20, ('A', 'B'): 35, ('A', 'C'): 30, ('A', 'W'): 35, ('A', 'BV'): 15, ('A', 'F'): 10
    }
    
    # Function to get travel time between two locations
    def get_travel_time(from_loc, to_loc):
        if from_loc == to_loc:
            return 0
        return travel_time_dict[(from_loc, to_loc)]
    
    # Build travel time matrix using the function
    travel_time_matrix = []
    for i in range(len(locations)):
        row = []
        for j in range(len(locations)):
            from_loc = locations[i]
            to_loc = locations[j]
            row.append(get_travel_time(from_loc, to_loc))
        travel_time_matrix.append(row)
    
    # Print travel time matrix
    print("Travel Time Matrix:")
    header = "       " + " ".join(f"{loc:>3}" for loc in locations)
    print(header)
    for i, loc in enumerate(locations):
        row_str = f"{loc}:    " + " ".join(f"{travel_time_matrix[i][j]:3}" for j in range(len(locations)))
        print(row_str)
    
    # Meetings data
    meetings = [
        {'name': 'Meeting1', 'location': 'B', 'duration': 30, 'earliest_arrival': 480, 'latest_arrival': 510, 'earliest_departure': 510, 'latest_departure': 540},
        {'name': 'Meeting2', 'location': 'W', 'duration': 60, 'earliest_arrival': 540, 'latest_arrival': 600, 'earliest_departure': 600, 'latest_departure': 660},
        {'name': 'Meeting3', 'location': 'BV', 'duration': 45, 'earliest_arrival': 600, 'latest_arrival': 660, 'earliest_departure': 645, 'latest_departure': 705},
        {'name': 'Meeting4', 'location': 'F', 'duration': 45, 'earliest_arrival': 660, 'latest_arrival': 720, 'earliest_departure': 705, 'latest_departure': 765},
        {'name': 'Meeting5', 'location': 'A', 'duration': 60, 'earliest_arrival': 720, 'latest_arrival': 780, 'earliest_departure': 780, 'latest_departure': 840}
    ]
    
    # Initialize Z3 solver
    s = Solver()
    
    # Create variables for arrival and departure times
    arrival_vars = [Int(f"arrival_{i}") for i in range(len(meetings))]
    departure_vars = [Int(f"departure_{i}") for i in range(len(meetings))]
    
    # Add constraints for each meeting
    for i, meeting in enumerate(meetings):
        s.add(arrival_vars[i] >= meeting['earliest_arrival'])
        s.add(arrival_vars[i] <= meeting['latest_arrival'])
        s.add(departure_vars[i] >= meeting['earliest_departure'])
        s.add(departure_vars[i] <= meeting['latest_departure'])
        s.add(departure_vars[i] == arrival_vars[i] + meeting['duration'])
    
    # Add travel time constraints between consecutive meetings
    for i in range(len(meetings) - 1):
        current_meeting = meetings[i]
        next_meeting = meetings[i + 1]
        travel_time = get_travel_time(current_meeting['location'], next_meeting['location'])
        s.add(arrival_vars[i + 1] >= departure_vars[i] + travel_time)
    
    # Check satisfiability
    if s.check() == sat:
        m = s.model()
        print("\nOptimal Schedule:")
        for i in range(len(meetings)):
            arrival_time = m[arrival_vars[i]].as_long()
            departure_time = m[departure_vars[i]].as_long()
            print(f"{meetings[i]['name']}: Arrival = {arrival_time}, Departure = {departure_time}")
    else:
        print("No valid schedule found")

if __name__ == "__main__":
    main()