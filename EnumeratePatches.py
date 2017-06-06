# Enumerating all patches of parcels with at least a given area.
# (c) James R. Wilcox 2017

# Parcel: atomic unit of land. Consists of:
#   - unique identifier
#   - area
#   - price (ignored for now)
#   - list of adjacent parcels
# See class Parcel below.

# Patch: a geographically contiguous set of parcels.
# See class Patch below.

import copy
import csv
import sys

# Main algorithm.
#
# The basic idea is to start with every parcel in its own patch, and
# then iteratively expand patches with adjacent parcels.
#
# The only tricky part is making sure you never consider the same
# patch twice.  One easy solution would be to check whether the patch
# had been seen before, but this wastes the work of generating it more
# than once.
#
# Instead, we keep track not only of which parcels have been added to
# the patch, but also which parcels have been considered but then
# *not* added.  When considering a patch's adjacent parcels, we leave
# out any that have already been considered.
def enumerate_patches(parcels, min_area):
    "Find all (minimal) patches with at least the given area"

    worklist = []

    # Initialize the worklist with all singleton patches.
    old_parcels = []
    for p in parcels:
        patch = Patch.singleton(p)
        patch.mark_all(old_parcels)
        worklist.append(patch)
        old_parcels.append(p)

    # Now start the actual processing.
    while len(worklist) > 0:
        patch = worklist.pop()

        # The problem asks for *minimal* patches, so once we hit the
        # area bound, we stop expanding.  "Stop expanding" here means
        # "don't put anything back on the worklist".
        if patch.area >= min_area:
            # That said, it is possible to reach this point with a
            # non-minimal patch.  For example, we could have added a
            # small parcel early on, that actually isn't necessary.
            # So we double check minimality here.
            if patch.is_minimal(min_area):
                yield patch

            # But in either case, we know we don't have to keep expanding.
            continue

        # Consider all possible one-step expansions of current patch.
        old_parcels = []
        for parcel in patch.adjacent():
            new_patch = copy.copy(patch)
            new_patch.add(parcel)
            new_patch.mark_all(old_parcels)

            worklist.append(new_patch)
            old_parcels.append(parcel)


class Parcel(object):
    """An atomic unit of land. Consists of:
       - unique identifier
       - area
       - price (ignored for now)
       - list of adjacent parcels"""

    # Since parcel ids are unique, we can look up a parcel by its id,
    # implemented by the following map.
    _instances = {}

    @staticmethod
    def fromId(id):
        "Look up the Parcel corresponding to the given id."
        return Parcel._instances[id]

    def __init__(self, id, area, price):
        if id in Parcel._instances:
            raise RuntimeError("duplicate parcel id {}".format(id))
        self.id = id
        self.area = area
        self.price = price

        # The list of adjacent parcels must be filled out elsewhere.
        self.adjacent = []

        Parcel._instances[id] = self

    def __str__(self):
        return "Parcel(id={}, area={}, price={})".format(self.id, self.area, self.price)

    def __repr__(self):
        return str(self)

class Patch(object):
    """A geographically contiguous set of parcels.
    The total area of the patch is available in the field `area`."""

    # Internally, a patch is represented as a dictionary mapping parcels to booleans.
    # If a parcel is mapped to True, then it is in the patch.
    # If it is mapped to False, then it is *marked* as considered, but not added.
    # Marked parcels are never considered adjacent to the patch.

    def __init__(self):
        self.parcels = {}
        self.area = 0

    def __str__(self):
        l = [p.id for (p, v) in self.parcels.iteritems() if v]
        l.sort()
        return "Patch({})".format(l)

    def __copy__(self):
        p = Patch()
        p.parcels = self.parcels.copy()
        p.area = self.area
        return p

    @staticmethod
    def singleton(parcel):
        "Construct a patch consisting of just the given parcel."
        result = Patch()
        result.add(parcel)
        return result

    def add(self, p):
        if p in self.parcels:
            raise RuntimeError("add parcel was already present")
        self.parcels[p] = True
        self.area += p.area

    def mark(self, p):
        """Mark a parcel as considered but *not* added.
        The parcel must not already be added present in the patch (either added or marked)."""
        if p in self.parcels:
            raise RuntimeError("mark parcel was already present")
        self.parcels[p] = False

    def mark_all(self, l):
        "Mark all parcels in the given list, if they are not already present."
        for p in l:
            self.mark(p)

    def adjacent(self):
        "A generator of (non-marked) parcels adjacent to this patch."
        visited = set()
        for (p, added) in self.parcels.iteritems():
            if added:
                for q in p.adjacent:
                    if q not in visited:
                        visited.add(q)
                        if q not in self.parcels:
                            yield q

    def is_minimal(self, min_area):
        for (p, present) in self.parcels.iteritems():
            if present and self.area - p.area >= min_area:
                return False

        return True

def load(parcel_file, adjacency_file):
    "Load parcel and adjacency data from the given files."
    parcels = []
    reader = csv.reader(parcel_file)
    for row in reader:
        parcel = Parcel(int(row[0]), float(row[1]), float(row[2]))
        parcels.append(parcel)

    reader = csv.reader(adjacency_file)
    for row in reader:
        a, b = Parcel.fromId(int(row[0])), Parcel.fromId(int(row[1]))
        a.adjacent.append(b)

    return parcels

def dump(dump_file, patches):
    """Dump patches to CSV file.
    The format is one patch per row.
    Each row consists of the list of parcel ids in that patch."""
    def patch_to_row(patch):
        l = [p.id for (p, present) in patch.parcels.items() if present]
        l.sort()
        return l

    l = [patch_to_row(patch) for patch in patches]
    l.sort()

    csv.writer(dump_file).writerows(l)


def main():
    # (Edit these paths to point to the data.)
    with open('/Users/jrw12/Downloads/Parcels.txt') as parcel_file, \
         open('/Users/jrw12/Downloads/Adjacency.txt') as adjacency_file:
         parcels = load(parcel_file, adjacency_file)

    patches = enumerate_patches(parcels, 50)

    # (Change `sys.stdout` to `open('/path/to/output/file', 'w')` to
    # write the data somewhere.)
    dump(sys.stdout, patches)

if __name__ == "__main__":
    main()
