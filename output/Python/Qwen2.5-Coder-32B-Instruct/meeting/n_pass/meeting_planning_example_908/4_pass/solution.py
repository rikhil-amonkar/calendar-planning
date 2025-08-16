travel_times = {
    "Financial District": {
        "Fisherman's Wharf": 10, "Presidio": 22, "Bayview": 19, "Haight-Ashbury": 19,
        "Russian Hill": 11, "The Castro": 20, "Marina District": 15, "Richmond District": 21,
        "Union Square": 9, "Sunset District": 30
    },
    "Fisherman's Wharf": {
        "Financial District": 11, "Presidio": 17, "Bayview": 26, "Haight-Ashbury": 22,
        "Russian Hill": 7, "The Castro": 27, "Marina District": 9, "Richmond District": 18,
        "Union Square": 13, "Sunset District": 27
    },
    "Presidio": {
        "Financial District": 23, "Fisherman's Wharf": 19, "Bayview": 31, "Haight-Ashbury": 15,
        "Russian Hill": 14, "The Castro": 21, "Marina District": 11, "Richmond District": 7,
        "Union Square": 22, "Sunset District": 15
    },
    "Bayview": {
        "Financial District": 19, "Fisherman's Wharf": 25, "Presidio": 32, "Haight-Ashbury": 19,
        "Russian Hill": 23, "The Castro": 19, "Marina District": 27, "Richmond District": 25,
        "Union Square": 18, "Sunset District": 23
    },
    "Haight-Ashbury": {
        "Financial District": 21, "Fisherman's Wharf": 23, "Presidio": 15, "Bayview": 18,
        "Russian Hill": 17, "The Castro": 6, "Marina District": 17, "Richmond District": 10,
        "Union Square": 19, "Sunset District": 15
    },
    "Russian Hill": {
        "Financial District": 11, "Fisherman's Wharf": 7, "Presidio": 14, "Bayview": 23,
        "Haight-Ashbury": 17, "The Castro": 21, "Marina District": 7, "Richmond District": 14,
        "Union Square": 10, "Sunset District": 23
    },
    "The Castro": {
        "Financial District": 21, "Fisherman's Wharf": 24, "Presidio": 20, "Bayview": 19,
        "Haight-Ashbury": 6, "Russian Hill": 18, "Marina District": 22, "Richmond District": 16,
        "Union Square": 19, "Sunset District": 17
    },
    "Marina District": {
        "Financial District": 17, "Fisherman's Wharf": 10, "Presidio": 10, "Bayview": 27,
        "Haight-Ashbury": 16, "Russian Hill": 8, "The Castro": 22, "Richmond District": 11,
        "Union Square": 16, "Sunset District": 19
    },
    "Richmond District": {
        "Financial District": 22, "Fisherman's Wharf": 18, "Presidio": 7, "Bayview": 27,
        "Haight-Ashbury": 10, "Russian Hill": 13, "The Castro": 16, "Marina District": 9,
        "Union Square": 21, "Sunset District": 11
    },
    "Union Square": {
        "Financial District": 9, "Fisherman's Wharf": 15, "Presidio": 24, "Bayview": 15,
        "Haight-Ashbury": 18, "Russian Hill": 13, "The Castro": 17, "Marina District": 18,
        "Richmond District": 20, "Sunset District": 27
    },
    "Sunset District": {
        "Financial District": 30, "Fisherman's Wharf": 29, "Presidio": 16, "Bayview": 22,
        "Haight-Ashbury": 15, "Russian Hill": 24, "The Castro": 17, "Marina District": 21,
        "Richmond District": 12, "Union Square": 30
    }
}

# Ensure symmetry in travel times
for loc1 in list(travel_times.keys()):
    for loc2 in list(travel_times[loc1].keys()):
        travel_times.setdefault(loc2, {})[loc1] = travel_times[loc1][loc2]

# Rest of the code remains the same