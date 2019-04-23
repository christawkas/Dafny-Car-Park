
// TODO use auto contract for every method!

class CarPark {

    // Set for lots that have been reserved
    var reservedSpace: set<int>;

    // Set for ltos that dont have a reservation on them
    var generalSpace: set<int>;

    // Maximum number of cars in overall 
    var maxSpots: int;

    // Set of cars that have a active reservation
    var carsWRes: set<int>;

    // Boolean for parking restriction
    var parkingRestriction: bool;


    // a constructor for the class, setting the car-park up for a new day.
    constructor (x: int)
    {
        maxSpots := x;

    }

    // to allow any car without a reservation to enter the car park.
    method enterCarPark (x: int) returns (res: bool)
    // requires that car does not exist in carparks
    requires !(x in generalSpace) && !(x in reservedSpace);
    //ensures that car is either in generalSpace or reservedSpace
    ensures x in generalSpace || x in reservedSpace
    //ensures that the collective sum of the two car spaces is 1 larger after the execution
    ensures |generalSpace|  == old(|generalSpace|) + 1
    ensures old(reservedSpace) == old(reservedSpace)
    modifies this;
    {
        generalSpace := generalSpace + {x};
        res := true;
    }

    // to allow any car from any area to leave the car park.
    // x is the id of the car
    method leaveCarPark(x: int)
    requires x in generalSpace || x in reservedSpace;
    // ensures that car is not in the sets anymore
    ensures !(x in generalSpace && x in reservedSpace);
    modifies this;
    {
        if(x in generalSpace) {
            generalSpace := generalSpace - {x};
        } else {
            reservedSpace := reservedSpace - {x};
        }
    }

    // to report on the number of non-reserved free spaces currently available.
    method checkAvailability () returns (res: int)
    requires true;
    ensures old(generalSpace) == generalSpace;
    ensures old(reservedSpace) == reservedSpace;
    {
        res := maxSpots - |generalSpace| - |reservedSpace|;
    }
    
    // to allow a car with a reservation to enter the car park’s reserved area during its hours of operation, or to enter the car park generally outside these hours.
    method enterReservedCarPark (x: int) returns (res: int)
    requires x in carsWRes
    requires parkingRestriction ==  true
    ensures old(|reservedSpace|) == |reservedSpace|-1;
    ensures old(generalSpace) == generalSpace;
    modifies this;
    {
        reservedSpace :=  reservedSpace + {x};
    }
    
    // to allow a car to be registered as having a reserved space when the owner pays the subscription.
    method makeSubscription (x: int) returns (res: int)
    {

    }

    // to remove parking restrictions on the reserved spaces (i.e. at 3pm).
    method openReservedArea() returns ()
    modifies this;
    {
        parkingRestriction := false;
    }

    // to remove and crush remaining parked cars at closing time.
    method closeCarPark() returns ()
    requires true;
    ensures |generalSpace| == 0 && |reservedSpace| == 0;
    modifies this;
    {
        generalSpace := {};
        reservedSpace := {};
    }

    // Valid() {
        
    // }
}
method Main ()  
{
    var cp := new CarPark(5);
    
}
