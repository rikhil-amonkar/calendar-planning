import z3
from itertools import permutations

# Define travel times in minutes
travel_times = {
    'Nob Hill': {
        'Embarcadero': 9,
        'The Castro': 17,
        'Haight-Ashbury': 13,
        'Union Square': 7,
        'North Beach': 8,
        'Pacific Heights': 8,
        'Chinatown': 6,
        'Golden Gate Park': 17,
        'Marina District': 11,
        'Russian Hill': 5,
    },
    'Embarcadero': {
        'Nob Hill': 10,
        'The Castro': 25,
        'Haight-Ashbury': 21,
        'Union Square': 10,
        'North Beach': 5,
        'Pacific Heights': 11,
        'Chinatown': 7,
        'Golden Gate Park': 25,
        'Marina District': 12,
        'Russian Hill': 8,
    },
    'The Castro': {
        'Nob Hill': 16,
        'Embarcadero': 22,
        'Haight-Ashbury': 6,
        'Union Square': 19,
        'North Beach': 20,
        'Pacific Heights': 16,
        'Chinatown': 22,
        'Golden Gate Park': 11,
        'Marina District': 21,
        'Russian Hill': 18,
    },
    'Haight-Ashbury': {
        'Nob Hill': 15,
        'Embarcadero': 20,
        'The Castro': 6,
        'Union Square': 19,
        'North Beach': 19,
        'Pacific Heights': 12,
        'Chinatown': 19,
        'Golden Gate Park': 7,
        'Marina District': 17,
        'Russian Hill': 17,
    },
    'Union Square': {
        'Nob Hill': 9,
        'Embarcadero': 11,
        'The Castro': 17,
        'Haight-Ashbury': 18,
        'North Beach': 10,
        'Pacific Heights': 15,
        'Chinatown': 7,
        'Golden Gate Park': 22,
        'Marina District': 18,
        'Russian Hill': 13,
    },
    'North Beach': {
        'Nob Hill': 7,
        'Embarcadero': 6,
        'The Castro': 23,
        'Union Square': 7,
        'Pacific Heights': 8,
        'Chinatown': 6,
        'Golden Gate Park': 22,
        'Marina District': 9,
        'Russian Hill': 4,
    },
    'Pacific Heights': {
        'Nob Hill': 8,
        'Embarcadero': 10,
        'The Castro': 16,
        'Haight-Ashbury': 11,
        'Union Square': 12,
        'North Beach': 9,
        'Chinatown': 11,
        'Golden Gate Park': 15,
        'Marina District': 6,
        'Russian Hill': 7,
    },
    'Chinatown': {
        'Nob Hill': 9,
        'Embarcadero': 5,
        'The Castro': 22,
        'Haight-Ashbury': 19,
        'Union Square': 7,
        'North Beach': 3,
        'Pacific Heights': 10,
        'Golden Gate Park': 23,
        'Marina District': 15,
        'Russian Hill': 7,
    },
    'Golden Gate Park': {
        'Nob Hill': 20,
        'Embarcadero': 25,
        'The Castro': 13,
        'Haight-Ashbury': 7,
        'Union Square': 22,
        'North Beach': 23,
        'Pacific Heights': 16,
        'Chinatown': 23,
        'Marina District': 16,
        'Russian Hill': 19,
    },
    'Marina District': {
        'Nob Hill': 12,
        'Embarcadero': 14,
        'The Castro': 22,
        'Haight-Ashbury': 16,
        'Union Square': 16,
        'North Beach': 11,
        'Pacific Heights': 7,
        'Chinatown': 15,
        'Golden Gate Park': 18,
        'Russian Hill': 8,
    },
    'Russian Hill': {
        'Nob Hill': 5,
        'Embarcadero': 8,
        'The Castro': 21,
        'Haight-Ashbury': 17,
        'Union Square': 10,
        'North Beach': 5,
        'Pacific Heights': 7,
        'Chinatown': 9,
        'Golden Gate Park': 21,
        'Marina District': 7,
    }
}

# Define friends and their details
friends = [
    ('Mary', 'Embarcadero', 75),
    ('Kenneth', 'The Castro', 30),
    ('Joseph', 'Haight-Ashbury', 120),
    ('Sarah', 'Union Square', 90),
    ('Thomas', 'North Beach', 15),
    ('Daniel', 'Pacific Heights', 15),
    ('Richard', 'Chinatown', 30),
    ('Mark', 'Golden Gate Park', 120),
    ('David', 'Marina District', 60),
    ('Karen', 'Russian Hill', 120)
]

friend_data = {}
for name, location, duration in friends:
    friend_data[name] = {'location': location, 'duration': duration, 'availability': (to_hours(9*60), to_hours(20*60 + 0))}

max_friends = 0

# Function to check if a schedule is feasible
def is_feasible(schedule):
    for friend in friends:
        name, location, duration = friend
        arrival_time = schedule.get((name, location), (0, 0))[0]
        departure_time = arrival_time + duration
        # Check if arrival time is within the friend's availability window
        start, end = friend_data[name]['availability']
        if not (start <= arrival_time <= end):
            return False
        # Check if departure time is after the required duration
        if departure_time < arrival_time + duration:
            return False
    return True

# Function to generate all possible schedules for a subset of friends
def generate_schedules(friends_subset):
    from itertools import product
    schedules = []
    # Generate all possible orders of friends in the subset
    for order in permutations(friends_subset):
        # For each friend in the order, calculate the arrival time based on previous meetings
        current_time = 540  # 9:00 AM in minutes
        schedule = {}
        for friend in order:
            name, location, duration = friend
            # Calculate the arrival time at the friend's location
            travel_time = travel_times['Nob Hill'][location]
            arrival_time = current_time + travel_time
            # Ensure arrival time is within the friend's availability window
            if not (friend_data[name]['availability'][0] <= arrival_time <= friend_data[name]['availability'][1]):
                break
            # Schedule the meeting
            meeting_end = arrival_time + duration
            schedule[(name, location)] = (arrival_time, meeting_end)
            current_time = meeting_end
        else:
            # If all friends in the subset are scheduled successfully
            schedules.append(schedule)
    return schedules

# Helper function to convert minutes to hours for Z3
def to_hours(time):
    return time // 60

# Helper function to convert hours to minutes
def to_minutes(time):
    return time * 60

# Main function to solve the problem
def solve():
    global max_friends
    max_friends = 0
    # Iterate over all possible subsets of friends
    for subset_size in range(1, len(friends)+1):
        for subset in combinations(friends, subset_size):
            # Generate all possible schedules for this subset
            schedules = generate_schedules(subset)
            for schedule in schedules:
                # Convert schedule to Z3 time variables
                variables = {}
                for (name, location), (arrival, departure) in schedule.items():
                    variables[(name, location)] = z3.Variable(f'meet_{name}_{location}')
                # Convert times to minutes
                # Presidio departure time is fixed at 9:00 AM (540 minutes)
                # For each friend, create constraints
                # This is a placeholder for actual constraints; in practice, more detailed constraints would be added
                # For example:
                # for (name, location), (arrival, departure) in schedule.items():
                #     # Ensure arrival is after previous departure
                #     # This is a simplified example
                #     # In practice, more complex constraints would be added
                #     # This is just a placeholder to demonstrate the function
                #     if arrival < previous_departure:
                #         return False
                #     variables[(name, location)] = arrival
                #     variables[(name, location)] = departure
                if is_feasible(schedule):
                    print(f"Feasible schedule found with {subset_size} friends")
                    max_friends = subset_size
                    return
    # If no feasible schedule is found, return 0
    return max_friends

# Run the solver
solve()

# Output the result
print(f"The maximum number of friends that can be met is {max_friends}")