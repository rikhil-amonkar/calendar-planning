import heapq

def format_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours:02d}:{minutes:02d}"

def to_minutes(time_str):
    hours, mins = map(int, time_str.split(':'))
    return hours * 60 + mins

# Read travel times
travel_times = {
    'Russian Hill': {
        'Pacific Heights': 7,
        'North Beach': 5,
        'Golden Gate Park': 21,
        'Embarcadero': 8,
        'Haight-Ashbury': 17,
        'Fisherman's Wharf': 7,
        'Mission District': 16,
        'Alamo Square': 15,
        'Bayview': 23,
        'Richmond District': 14,
    },
    'Pacific Heights': {
        'Russian Hill': 7,
        'North Beach': 9,
        'Golden Gate Park': 15,
        'Embarcadero': 10,
        'Haight-Ashbury': 11,
        'Fisherman's Wharf': 13,
        'Mission District': 15,
        'Alamo Square': 10,
        'Bayview': 22,
        'Richmond District': 12,
    },
    'North Beach': {
        'Russian Hill': 4,
        'Pacific Heights': 8,
        'Golden Gate Park': 22,
        'Embarcadero': 6,
        'Haight-Ashbury': 18,
        'Fisherman's Wharf': 5,
        'Mission District': 18,
        'Alamo Square': 16,
        'Bayview': 25,
        'Richmond District': 18,
    },
    'Golden Gate Park': {
        'Russian Hill': 19,
        'Pacific Heights': 16,
        'North Beach': 23,
        'Embarcadero': 25,
        'Haight-Ashbury': 7,
        'Fisherman's Wharf': 24,
        'Mission District': 17,
        'Alamo Square': 9,
        'Bayview': 23,
        'Richmond District': 7,
    },
    'Embarcadero': {
        'Russian Hill': 8,
        'Pacific Heights': 11,
        'North Beach': 5,
        'Golden Gate Park': 25,
        'Haight-Ashbury': 20,
        'Fisherman's Wharf': 6,
        'Mission District': 19,
        'Alamo Square': 16,
        'Bayview': 21,
        'Richmond District': 21,
    },
    'Haight-Ashbury': {
        'Russian Hill': 17,
        'Pacific Heights': 12,
        'North Beach': 19,
        'Golden Gate Park': 7,
        'Embarcadero': 20,
        'Fisherman's Wharf': 23,
        'Mission District': 11,
        'Alamo Square': 5,
        'Bayview': 18,
        'Richmond District': 10,
    },
    'Fisherman's Wharf': {
        'Russian Hill': 7,
        'Pacific Heights': 12,
        'North Beach': 6,
        'Golden Gate Park': 25,
        'Embarcadero': 8,
        'Haight-Ashbury': 22,
        'Mission District': 22,
        'Alamo Square': 21,
        'Bayview': 26,
        'Richmond District': 18,
    },
    'Mission District': {
        'Russian Hill': 15,
        'Pacific Heights': 16,
        'North Beach': 17,
        'Golden Gate Park': 17,
        'Embarcadero': 19,
        'Haight-Ashbury': 12,
        'Fisherman's Wharf': 22,
        'Alamo Square': 11,
        'Bayview': 14,
        'Richmond District': 20,
    },
    'Alamo Square': {
        'Russian Hill': 13,
        'Pacific Heights': 10,
        'North Beach': 15,
        'Golden Gate Park': 9,
        'Embarcadero': 16,
        'Haight-Ashbury': 5,
        'Fisherman's Wharf': 19,
        'Mission District': 10,
        'Bayview': 16,
        'Richmond District': 11,
    },
    'Bayview': {
        'Russian Hill': 23,
        'Pacific Heights': 23,
        'North Beach': 22,
        'Golden Gate Park': 22,
        'Embarcadero': 19,
        'Haight-Ashbury': 19,
        'Fisherman's Wharf': 25,
        'Mission District': 13,
        'Alamo Square': 16,
        'Richmond District': 25,
    },
    'Richmond District': {
        'Russian Hill': 13,
        'Pacific Heights': 10,
        'North Beach': 17,
        'Golden Gate Park': 9,
        'Embarcadero': 19,
        'Haight-Ashbury': 10,
        'Fisherman's Wharf': 18,
        'Mission District': 20,
        'Alamo Square': 13,
        'Bayview': 27,
    }
}

# Read people data and convert times to minutes
people = [
    {
        'name': 'Emily',
        'location': 'Pacific Heights',
        'availability_start': '9:15',
        'availability_end': '13:45',
        'required_time': 120
    },
    {
        'name': 'Helen',
        'location': 'North Beach',
        'availability_start': '13:45',
        'availability_end': '18:45',
        'required_time': 30
    },
    {
        'name': 'Kimberly',
        'location': 'Golden Gate Park',
        'availability_start': '18:45',
        'availability_end': '21:15',
        'required_time': 75
    },
    {
        'name': 'James',
        'location': 'Embarcadero',
        'availability_start': '10:30',
        'availability_end': '11:30',
        'required_time': 30
    },
    {
        'name': 'Linda',
        'location': 'Haight-Ashbury',
        'availability_start': '7:30',
        'availability_end': '19:15',
        'required_time': 15
    },
    {
        'name': 'Paul',
        'location': 'Fisherman's Wharf',
        'availability_start': '14:45',
        'availability_end': '18:45',
        'required_time': 90
    },
    {
        'name': 'Anthony',
        'location': 'Mission District',
        'availability_start': '8:00',
        'availability_end': '14:45',
        'required_time': 105
    },
    {
        'name': 'Nancy',
        'location': 'Alamo Square',
        'availability_start': '8:30',
        'availability_end': '13:45',
        'required_time': 120
    },
    {
        'name': 'William',
        'location': 'Bayview',
        'availability_start': '17:30',
        'availability_end': '20:30',
        'required_time': 120
    },
    {
        'name': 'Margaret',
        'location': 'Richmond District',
        'availability_start': '15:15',
        'availability_end': '18:15',
        'required_time': 45
    }
]

for person in people:
    person['availability_start'] = to_minutes(person['availability_start'])
    person['availability_end'] = to_minutes(person['availability_end'])

# Initialize priority queue
priority_queue = []

for person in people:
    from_loc = 'Russian Hill'
    to_loc = person['location']
    arrival_time = 540 + travel_times[from_loc][to_loc]
    avail_start = person['availability_start']
    avail_end = person['availability_end']
    required = person['required_time']
    
    earliest_start = max(arrival_time, avail_start)
    latest_start = avail_end - required
    
    if earliest_start <= latest_start:
        heapq.heappush(priority_queue, (earliest_start, earliest_start + required, person))

schedule = []
current_end = 540  # 9:00 AM in minutes

while priority_queue:
    start_min, end_min, person = heapq.heappop(priority_queue)
    
    # Check if this meeting can be scheduled
    if start_min >= current_end:
        # Check if the meeting ends before the person's availability end
        if end_min <= person['availability_end']:
            # Add to schedule
            schedule.append({
                'action': 'meet',
                'location': person['location'],
                'person': person['name'],
                'start_time': format_time(start_min),
                'end_time': format_time(end_min)
            })
            current_end = end_min
            
            # Check for more possible meetings
            for p in people:
                from_loc = 'Russian Hill'
                to_loc = p['location']
                arrival_time = 540 + travel_times[from_loc][to_loc]
                avail_start = p['availability_start']
                avail_end = p['availability_end']
                required = p['required_time']
                
                earliest_start = max(arrival_time, avail_start)
                latest_start = avail_end - required
                
                if earliest_start <= latest_start:
                    if earliest_start >= current_end:
                        heapq.heappush(priority_queue, (earliest_start, earliest_start + required, p))
    else:
        # This meeting can't be scheduled now, put it back into the queue
        heapq.heappush(priority_queue, (start_min, end_min, person))

# Convert the schedule to the required format
itinerary = []
for meeting in schedule:
    location = meeting['location']
    person = meeting['person']
    start = meeting['start_time']
    end = meeting['end_time']
    itinerary.append({
        'action': 'meet',
        'location': location,
        'person': person,
        'start_time': start,
        'end_time': end
    })

# Convert itinerary to JSON
import json
print(json.dumps({
    "itinerary": itinerary
}))