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
    
    # Create variables for arrival times
    arrival_vars = [Int(f"arrival_{i}") for i in range(len(meetings))]
    
    # Add constraints for each meeting
    for i, meeting in enumerate(meetings):
        # Constrain arrival time within window
        s.add(arrival_vars[i] >= meeting['earliest_arrival'])
        s.add(arrival_vars[i] <= meeting['latest_arrival'])
        
        # Calculate and constrain departure time
        departure = arrival_vars[i] + meeting['duration']
        s.add(departure >= meeting['earliest_departure'])
        s.add(departure <= meeting['latest_departure'])
    
    # Add travel time constraints between consecutive meetings
    for i in range(len(meetings) - 1):
        travel_time = get_travel_time(meetings[i]['location'], meetings[i+1]['location'])
        s.add(arrival_vars[i+1] >= arrival_vars[i] + meetings[i]['duration'] + travel_time)
    
    # Check satisfiability
    if s.check() == sat:
        m = s.model()
        print("Optimal Schedule:")
        for i in range(len(meetings)):
            arrival_time = m[arrival_vars[i]].as_long()
            departure_time = arrival_time + meetings[i]['duration']
            # Convert times to HH:MM format
            arr_hour = arrival_time // 60
            arr_min = arrival_time % 60
            dep_hour = departure_time // 60
            dep_min = departure_time % 60
            print(f"{meetings[i]['name']}: Arrival = {arr_hour:02d}:{arr_min:02d}, Departure = {dep_hour:02d}:{dep_min:02d}")
    else:
        print("No valid schedule found")

if __name__ == "__main__":
    main()