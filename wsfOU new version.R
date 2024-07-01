install.packages("pracma")
install.packages("MASS")
install.packages("mvtnorm")
install.packages("optimr")
install.packages("bbmle")
install.packages("mle.tools")
install.packages("plot3D")
install.packages("rworldmap")
install.packages("geosphere")
install.packages("maxLik")
install.packages("zipfR")
install.packages("bdsmatrix")
install.packages("float")
install.packages("cubature")
install.packages("scModels")
install.packages("hypergeo")
install.packages("expint")
install.packages("PrevMap")

# Install and load fields
install.packages("fields")
library(fields)


#----Library Packages
library(maxLik)
library(pracma)
library(MASS)
library(mvtnorm)
library(optimr)
library(bbmle)
library(mle.tools)
library(plot3D)
library(rworldmap)
library(geosphere)
library(zipfR)
library(bdsmatrix)
    library(float)
    library(cubature)
    library(scModels)
    library(hypergeo)
    library(expint)
    library(PrevMap)
   
  

#----Auxiliar function to covariance weighted

D_1<-function(u,s,t,a,b) {#----Delta function
   return( (1/(1-b)) *(u^a) *(  (t-u)^b+(s-u)^b-(t+s-2*u)^b ) ) 
} 



D_2<-function(u,s,t,a) {#----Delta function
	aux<-0
	if(as.numeric(min(s,t))!=as.numeric(u)){
        aux<-(u^a)*(  -(t-u)*log(t-u)-(s-u)*log(s-u)+(t+s-2*u)*log(t+s-2*u) ) 
     }
    else{
       if(as.numeric(min(s,t))!=as.numeric(max(s,t))){
 	   aux<-(u^a)*(  -(max(s,t)-u)*log(max(s,t)-u)+(max(s,t)+min(s,t)-2*u)*log(max(s,t)+min(s,t)-2*u) ) 
       }
    }
    return(aux)
} 


D_4<-function(u,s,t,a) {#----Delta function
    sapply(u,function(y){
     aux<-0	
     if(as.numeric(min(s,t))!=as.numeric(y)){
              aux<-(y^a)*(  -(t-y)*log(t-y)-(s-y)*log(s-y)+(t+s-2*y)*log(t+s-2*y) ) 
              return(aux)
        }
      else{ 
        return(aux)
      }
      })
} 
 



D_3<-function(u,s,t,a,b) {#----Delta function
   return( (1/(1-b)) *(exp(u*a)) *(  (t-u)^b+(s-u)^b-(t+s-2*u)^b ) ) 
} 


pol_log_int_2<-function(x,a){
    	aux<-0
	    if(as.numeric(a)>0){
	        aux<-(exp(a*x)*((a*(1-x)+1)*log(1-x)+1)+exp(a)*(gammainc(0,a*(1-x))-gammainc(0,a))-1)/(a^2)
	    }
	    else{
		   aux<-(exp(a*x)*((a*(1-x)+1)*log(1-x)+1)+exp(a)*(expint_Ei(-a)-expint_Ei(a*(x-1)))-1)/(a^2)
	    }
	   return(aux)
}

pol_log_int_1<-function(x,a){
 	aux<-0
	aux<-(exp(a*x)*(-a*x+a+1)-a-1)/(a^2)
	return(aux)
}

gamma_2<-function(a){
	if(as.numeric(a)>0){
     	return((-exp(a)*(gammainc(0,a)-digamma(1)-1+log(a))-1)/(a^2))
	}
	else{
		return(-exp(a)*(-expint_Ei(-a)-digamma(1)-1+log(-a)+exp(-a))/(a^2))
	}
}





gamma_1<-function(a){
	return((exp(a)-(1+a))/(a^2))
}


sub_frac<-function(s,t,b){
    aux<-(1/(1-b^2))*(t^(b+1)+s^(b+1)-0.5*((t+s)^(b+1)+(max(s,t)-min(s,t))^(b+1)))
    return(aux)	
}


sub_frac_log<-function(s,t){
	aux<-0
	if(as.numeric(min(s,t))!=0){
		if(as.numeric(s)!=as.numeric(t)){
             aux<-(-0.5)*((s^2)*log(s)+(t^2)*log(t)-0.5*(((s+t)^2)*log(s+t) +((s-t)^2)*log(max(s,t)-min(s,t))    )    ) 
        }
        else{
        	aux<-(-0.5)*((s^2)*log(s)+(t^2)*log(t)-0.5*((s+t)^2)*log(s+t)         )
        }
     }
    return(aux)
}





#--------Covariance weithed in one point:

covariance_function<-function(s,t,a,b,c){ #---time is vector of times
if(as.numeric(a)!=0){
	if(as.numeric(c)==0){                   #---a,b parameters, c family #---Polinomial
	      if(as.numeric(b)!=1){ #----weithed
	           aux<-0
               if(as.numeric(max(s,t))!=0){
                        aux<-(1/(1-b))*((min(s,t)^(a+b+1))*beta(a+1, b+1)+(max(s,t)^(a+b+1))*Ibeta(min(s,t)/max(s,t), a+1, b+1)-1*(2^(-1-a))*((min(s,t)+max(s,t))^(a+b+1))*Ibeta(2*min(s,t)/(min(s,t)+max(s,t)), a+1, b+1))
               } 
        return(aux)
          }                                
		else{            #----Logaritmo
    		   if(as.numeric(s)!=as.numeric(t)){
    		     sapply(min(s,t),function(y){
    		 	      g<-function(z){
                         return(D_4(z,s=s,t=t,a=a))#---t_1 parametro de h
                     }
                     return(integrate(g,0,y)$val)
                 }
                )	
		      }
		     else{
		     	aux<-0
		     	aux<-2*log(2)*(t^(a+2))*beta(a+1,2)
		     	return(aux)	
		     }
		   }
		
	}
	else{#----Exponencial
		if(as.numeric(b)!=1){ #---weithed
	      	if(as.numeric(a)>0){ #---a>0
	      		aux<-0
                if(as.numeric(max(s,t))!=0){
                    aux<-(1/((1-b)*(a^(b+1))))*(
                    exp(a*min(s,t))*(gammainc(b+1,0)-gammainc(b+1,a*min(s,t)))
                    +exp(a*max(s,t))*(gammainc(b+1,a*(max(s,t)-min(s,t)))-gammainc(b+1,a*max(s,t)))
                    -(2^b)*exp(a*(max(s,t)+min(s,t))/2)*(gammainc(b+1,a*(max(s,t)-min(s,t))/2)-gammainc(b+1,a*(max(s,t)+min(s,t))/2))
                    )
                } 
            return(aux)
            }
	       else{                 #-----a<0
	              sapply(min(s,t),function(y){
	           	    g<-function(z){
                       return(D_3(z,s=s,t=t,a=a,b=b))#---t_1 parametro de h
                    }
                    return(integrate(g,0,y)$val)
                    }
                   )
               
	        
	        } 
	      }                                
		else{                 #----logaritmo
		  aux<-0
          if(as.numeric(min(s,t))!=0){
              if(as.numeric(s)!=as.numeric(t)) {
                  aux<-( (2^(-1))*((min(s,t)+max(s,t))^(2))*( log(min(s,t)+max(s,t))*pol_log_int_1(2*min(s,t)/(min(s,t)+max(s,t)),a*(min(s,t)+max(s,t))/2) + pol_log_int_2(2*min(s,t)/(min(s,t)+max(s,t)),a*(min(s,t)+max(s,t))/2))
     	         -(max(s,t)^(2))*(log(max(s,t))*pol_log_int_1(min(s,t)/max(s,t),a*max(s,t))+  pol_log_int_2(min(s,t)/max(s,t),a*max(s,t)) )
     	         -(min(s,t)^(2))*(log(min(s,t))*gamma_1(a*min(s,t))+ gamma_2(a*min(s,t)) ) )        
              }
          else{
     	     g_1<-gamma_1(a*s)
     	     g_2<-gamma_2(a*s)
     	     aux<-( (2^(-1))*((min(s,t)+max(s,t))^(2))*( log(min(s,t)+max(s,t))*g_1 + g_2)
     	     -(max(s,t)^(2))*(log(max(s,t))*g_1+  g_2 )
     	     -(min(s,t)^(2))*(log(min(s,t))*g_1+ g_2 ) )  
         } 
        }
        return(aux)
	   }
    }
   }
   else{  #---a=0
   	   if(as.numeric(b)!=1){ #-subfraccionario
   	         	aux<-sub_frac(s,t,b)
   	         	return(aux)
   		  }
   	   else{      #---subfraccionario log
   		aux<-sub_frac_log(s,t)
   	    return(aux)
   	  }
   }
}


#--------------------Covariance weighted

cov_wfbm<-function(time,a,b,c){
  n<-length(time)
  K<-matrix(rep(0,n*n),n,n)
    for(i in 1:n) {
      for(j in 1:i) {
        K[i,j]<-covariance_function(time[i],time[j],a,b,c)
        K[j,i]<-K[i,j]
      } 
    }
  return(K) 
 } 


#------Simulation

simulation<-function(time,a,b,c){
	n<-length(time)
	mean<-rep(0,n)
	K<-cov_wfbm(time,a,b,c)
return(rmvnorm(1,mean,K))	
}


#-------log likelihood

log_verosimilitude<-function(time,data,a,b,c){
n<-length(time)
K<-cov_wfbm(time,a,b,c)
return(dmvnorm(data,rep(0,n),K,log=TRUE))
}

#----Prediction

prediction<-function(time,time_2,data,a,b,c,sim){
n<-length(time)    #----sim numero de simulaciones
m<-length(time_2)+n
K<-cov_wfbm(c(time,time_2),a,b,c)
step<-m-n
K_11<-K[1:n,1:n]
K_12<-K[1:n,(n+1):(n+step)]
K_21<-t(K[1:n,(n+1):(n+step)])
K_22<-K[(n+1):(n+step),(n+1):(n+step)]
K_11_inv<-solve(K_11)
S<-K_22-K_21%*%K_11_inv%*%K_12
predic<-rmvnorm(sim,K_21%*%K_11_inv%*%data,(S+t(S))/2)
return(predic)
}




#-----Examples and inference------

#------Polinomial case:

T<-10
n<-500
D<-T/n
b<-1.59
a<-0.42
c<-0
time<-seq(D,T,length=n)
sim<-as.numeric(simulation(time,a,b,c)[1,])
initial<-0
plot(c(0,time),c(initial,sim),type="l",xlab="time",ylab=" ")




#-----delta porcentaje de la data para hacer inferencia

delta<-0.9
n<-int(n*delta)
T<-D*n
sim_dat<-sim[1:n]
time<-seq(D,T,length=n)
initial<-0
plot(c(0,time),c(initial,sim_dat),type="l",xlab="time",ylab=" ")



write.csv(sim,"sim_data_wsfBm_pol.csv")


log_verosimilitude(time,sim_dat,a,b,c)



#------------Change to polinomial family---------------
log_vero<-function(x){
-log_verosimilitude(time,sim_dat,x[1],x[2],c=0)
}



t <- proc.time()
block<-40
reg_a<-seq(-0.90,0.90,length=block)
reg_b<-seq(0.05,1.95,length=block)
profile<-matrix(rep(0,block*block),block,block)
for(i in 1:block){
 for(j in 1:block){
   profile[i,j]<-log_vero(c(reg_a[i],reg_b[j]))
 }
}

res<-persp(reg_a,reg_b,exp((-profile-max_profile)/200),theta = 35, phi = 60,xlab="a",ylab="b",zlab=" ")
x <- c(max[1])
y <- c(max[2])
z <- c(1)
mypoints <- trans3d(x,y,z,pmat = res)
points(mypoints,pch = 19,col = "red")

proc.time()-t



#-----MLE calculations

a
b

log_vero(c(a,b))
max<-rep(0,2)

maximos<-opm(c(runif(1,0,1),runif(1,1,2)),fn=log_vero, lower=c(0.05,0.05), upper=c(1.95,1.95),method="L-BFGS-B")
 max[1]<-maximos$p1
 max[2]<-maximos$p2


max_profile<--log_vero(max)



log_vero_a<-function(x){
log_verosimilitude(time,sim_dat,x,max[2],c=0)
}


log_vero_b<-function(x){
log_verosimilitude(time,sim_dat,max[1],x,c=0)
}



block<-100
reg_a<-seq(0.34,0.65,length=block)
reg_b<-seq(1.54,1.68,length=block)
profile_a<-rep(0,block)
profile_b<-rep(0,block)
for(i in 1:block){
	profile_a[i]<-log_vero_a(reg_a[i])
	profile_b[i]<-log_vero_b(reg_b[i])
}

par(mfrow=c(1,2))
f<-qchisq(0.9746794,1)

like_ratio_b<-function(x){
	-2*(log_vero_b(x)-max_profile)-f
}





#-----Profile funcion-----

#root_b_l<-uniroot(like_ratio_b,lower=1,upper=max[2],tol=1e-9)$root
#root_b_r<-uniroot(like_ratio_b,lower=max[2],upper=2,tol=1e-9)$root


#norm_2<-1/(-hessian(log_vero_b,max[2]))
#normal_approx_2<-dnorm(reg_b,max[2],sqrt(norm_2))

#valc1_1<-qnorm(0.005,max[2],sqrt(norm_2))
#valc2_1<-qnorm(0.995,max[2],sqrt(norm_2))
#val1<-dnorm(valc1_1,max[2],sqrt(norm_2))

plot(reg_b,exp(profile_b-max_profile),type="l",,xlab=expression(b),ylab=expression(paste("Profile Likelihood Ratio ",b)),col="blue",lwd=2,cex.main=2,cex.lab=1.2)
lines(c(max[2],max[2]),c(0,3000),col="red",lwd=2)
lines(c(b,b),c(0,3000),col="yellow",lwd=2)
lines(c(root_b_l,root_b_l),c(0,15),col="green",lwd=2)
lines(c(root_b_r,root_b_r),c(0,15),col="green",lwd=2)

#lines(c(valc1_1,valc1_1),c(0,3000),col="green",lwd=2)
#lines(c(valc2_1,valc2_1),c(0,3000),col="green",lwd=2)






#norm_1<-1/(-hessian(log_vero_a,max[1]))
#normal_approx_1<-dnorm(reg_a,max[1],sqrt(norm_1))



#valc1_1<-qnorm(0.005,max[1],sqrt(norm_1))
#valc2_1<-qnorm(0.995,max[1],sqrt(norm_1))
#val1<-dnorm(valc1_1,max[1],sqrt(norm_1))


like_ratio_a<-function(x){
	-2*(log_vero_a(x)-max_profile)-f
}

#root_a_r<-uniroot(like_ratio_a,lower=max[1],upper=1,tol=1e-9)$root
#root_a_l<-uniroot(like_ratio_a,lower=0.1,upper=max[1],tol=1e-9)$root




plot(reg_a,exp(profile_a-max_profile),type="l",xlab=expression(a),ylab=expression(paste("Profile Likelihood Ratio ",a)),col="blue",lwd=2,cex.main=2,cex.lab=1.2)
lines(c(max[1],max[1]),c(0,3000),col="red",lwd=2)
lines(c(root_a_l,root_a_l),c(0,15),col="green",lwd=2)
lines(c(root_a_r,root_a_r),c(0,15),col="green",lwd=2)
lines(c(a,a),c(0,3000),col="yellow",lwd=2)
#lines(c(valc2_1,valc2_1),c(0,3000),col="green",lwd=2)


#lines(reg_a,exp(profile_a-max_profile)*(1/(sqrt(norm_1*2*pi))),col="black",lwd=2)

#----End polinomial case------


#----Exponential case:

log_vero<-function(x){
-log_verosimilitude(time,sim_dat,x[1],x[2],c=1)
}

t <- proc.time()
block<-40
reg_a<-seq(-0.90,0.90,length=block)
reg_b<-seq(1.2,1.31,length=block)
profile<-matrix(rep(0,block*block),block,block)
for(i in 1:block){
 for(j in 1:block){
   profile[i,j]<-log_vero(c(reg_a[i],reg_b[j]))
 }
}

res<-persp(reg_a,reg_b,exp((-profile-max_profile)/200),theta = 35, phi = 60,xlab="a",ylab="b",zlab=" ")
x <- c(max[1])
y <- c(max[2])
z <- c(1)
mypoints <- trans3d(x,y,z,pmat = res)
points(mypoints,pch = 19,col = "red")

proc.time()-t



#-----MLE calculations


max<-rep(0,2)
maximos<-opm(c(runif(1,-0.6,0.6),runif(1,0.05,1.95)),fn=log_vero, lower=c(-0.6,0.05), upper=c(0.6,1.95),method="L-BFGS-B")
 max[1]<-maximos$p1
 max[2]<-maximos$p2

max_profile<--log_vero(max)


log_vero_a<-function(x){
log_verosimilitude(time,sim_dat,x,max[2],c=1)
}


log_vero_b<-function(x){
log_verosimilitude(time,sim_dat,max[1],x,c=1)
}



block<-100
reg_a<-seq(-0.5,-0.15,length=block)
reg_b<-seq(1.18,1.33,length=block)
profile_a<-rep(0,block)
profile_b<-rep(0,block)
for(i in 1:block){
	profile_a[i]<-log_vero_a(reg_a[i])
	profile_b[i]<-log_vero_b(reg_b[i])
}

par(mfrow=c(1,2))
f<-qchisq(0.9746794,1)

like_ratio_b<-function(x){
	-2*(log_vero_b(x)-max_profile)-f
}

#root_b_l<-uniroot(like_ratio_b,lower=0.92,upper=max[2],tol=1e-9)$root
#root_b_r<-uniroot(like_ratio_b,lower=max[2],upper=1.6,tol=1e-9)$root


#norm_2<-1/(-hessian(log_vero_b,max[2]))
#normal_approx_2<-dnorm(reg_b,max[2],sqrt(norm_2))

#valc1_1<-qnorm(0.005,max[2],sqrt(norm_2))
#valc2_1<-qnorm(0.995,max[2],sqrt(norm_2))
#val1<-dnorm(valc1_1,max[2],sqrt(norm_2))

plot(reg_b,exp(profile_b-max_profile),type="l",,xlab=expression(b),ylab=expression(paste("Profile Likelihood Ratio ",b)),col="blue",lwd=2,cex.main=2,cex.lab=1.2)
lines(c(max[2],max[2]),c(0,3000),col="red",lwd=2)
lines(c(b,b),c(0,3000),col="yellow",lwd=2)
lines(c(root_b_l,root_b_l),c(0,15),col="green",lwd=2)
lines(c(root_b_r,root_b_r),c(0,15),col="green",lwd=2)

#lines(c(valc1_1,valc1_1),c(0,3000),col="green",lwd=2)
#lines(c(valc2_1,valc2_1),c(0,3000),col="green",lwd=2)






#norm_1<-1/(-hessian(log_vero_a,max[1]))
#normal_approx_1<-dnorm(reg_a,max[1],sqrt(norm_1))



#valc1_1<-qnorm(0.005,max[1],sqrt(norm_1))
#valc2_1<-qnorm(0.995,max[1],sqrt(norm_1))
#val1<-dnorm(valc1_1,max[1],sqrt(norm_1))


like_ratio_a<-function(x){
	-2*(log_vero_a(x)-max_profile)-f
}

#root_a_r<-uniroot(like_ratio_a,lower=max[1],upper=-0.1,tol=1e-9)$root
#root_a_l<-uniroot(like_ratio_a,lower=-0.6,upper=max[1],tol=1e-9)$root




plot(reg_a,exp(profile_a-max_profile),type="l",xlab=expression(a),ylab=expression(paste("Profile Likelihood Ratio ",a)),col="blue",lwd=2,cex.main=2,cex.lab=1.2)
lines(c(max[1],max[1]),c(0,3000),col="red",lwd=2)
lines(c(root_a_l,root_a_l),c(0,15),col="green",lwd=2)
lines(c(root_a_r,root_a_r),c(0,15),col="green",lwd=2)
lines(c(a,a),c(0,3000),col="yellow",lwd=2)
#lines(c(valc2_1,valc2_1),c(0,3000),col="green",lwd=2)


#lines(reg_a,exp(profile_a-max_profile)*(1/(sqrt(norm_1*2*pi))),col="black",lwd=2)


#------------Change to lon data---------------
log_vero<-function(x){
-log_verosimilitude(time,sim_dat,x,1,c=1)
}




#maximos<-opm(runif(1,-1,1),,fn=log_vero, lower=-0.95, upper=2,method="L-BFGS-B")
max_a<-maximos$p1
block<-200
reg_a<-seq(-0.02,0.06,length=block)
profile_a<-rep(0,block)
for(i in 1:block){
	profile_a[i]<--log_vero(reg_a[i])
	
}
max_pa<--log_vero(max_a)

plot(reg_a,exp(profile_a-max_pa),type="l",xlab=expression(a),ylab=expression(paste("Profile Likelihood Ratio ",a)),col="blue",lwd=2,cex.main=2,cex.lab=1.2)


like_ratio_a<-function(x){
	-2*(-log_vero(x)-max_pa)-f
}

root_a_r<-uniroot(like_ratio_a,lower=max_a,upper=0.06,tol=1e-9)$root
root_a_l<-uniroot(like_ratio_a,lower=-0.02,upper=max_a,tol=1e-9)$root




plot(reg_a,exp(profile_a-max_pa),type="l",xlab=expression(a),ylab=expression(paste("Profile Likelihood Ratio ",a)),col="blue",lwd=2,cex.main=2,cex.lab=1.2)
lines(c(max_a,max_a),c(0,3000),col="red",lwd=2)
lines(c(root_a_l,root_a_l),c(0,15),col="green",lwd=2)
lines(c(root_a_r,root_a_r),c(0,15),col="green",lwd=2)
lines(c(0,0),c(0,3000),col="yellow",lwd=2)




#------Predictions



b<-max[2]
a<-max[1]
c<-0
time_2<-seq(10/500,10,length=500)[(n+1):500]
number_sim<-1000
predic<-prediction(time,time_2,sim_dat,a,b,c,number_sim)
step<-length(time_2)

medias_pred<-rep(0,step)


for(i in 1:step) {
   medias_pred[i]<-mean(predic[,i])
}


max<-max(sim_dat)+abs(max(predic)-sim_dat[n])
min<-min(sim_dat)-abs(min(predic)-sim_dat[n])
plot(c(time,time_2),sim,type="l",col="black",xlab="t",ylab=" ",ylim=c(min,max),lwd=2)

points(0,0,col="red",pch=19)
points(time[n],sim_dat[n],col="blue",pch=19)



interval_l<-rep(0,step)
interval_r<-rep(0,step)


conf<-0.95


for(i in 1:step){
interval_l[i]<-as.numeric(quantile(predic[,i],(1-conf)/2))
interval_r[i]<-as.numeric(quantile(predic[,i],1-(1-conf)/2))
}

for(i in 1:number_sim){
	lines(time_2,predic[i,],type="l",col="gray",lwd=1)
}


lines(time_2,interval_l,col="brown",lwd=2)
lines(time_2,interval_r,col="brown",lwd=2)


lines(time_2,medias_pred,type="l",col="yellow",lwd=2)

lines(time_2,sim[(n+1):(n+step)],col="orange",lwd=2)



legend("topleft", legend=c("Initial Position","Final Position","Trajectory","Trajectory Predicted Mean","Trajectory to Predict", "95% Confidence Bands", "Predictions"),
       col=c("Red","blue","black","Yellow","orange","Brown","gray"),pch = c(19,19,NA,NA,NA,NA,NA), lty = c(NA,NA,1, 1, 1,1,1),cex=0.8)



norm<-function(x,y){
	n<-length(x)
	aux<-0
	for(i in 1:n){
		aux<-aux+(x[i]-y[i])^2
	}
return(sqrt(aux))
}



e_cuad<-rep(0,step)
for(i in 1:step){
	e_cuad[i]<-norm(medias_pred[i],sim[n+i])^2
}

#---AIC
4+2*log_vero(c(a,b))
#----Eroor cuadratico medio
mean(e_cuad)


#-----End exponential case

#---End examples-----






#---------wsbfOU------------------------



G<-function(beta,a,b,c,s,t,u,v){return(exp(-beta*(u+v))*covariance_function(s-u,t-v,a,b,c))
	
	}


H<-function(beta,a,b,c,s,t,u){return(exp(-beta*u)*covariance_function(s-u,t,a,b,c))
	
	}



tol<-1e-4





H_aux_OU<-function(beta,a,b,c,s,t,D)
{
	H_aux<-function(x) {
                return(H(beta=beta,a=a,b=b,c=c,s=s,t=t,x))#---t_1 parametro de h
              }
         return(pcubature(H_aux,0,D,tol=tol)$integral)
} 



G_aux_OU<-function(beta,a,b,c,s,t,D1,D2)
{
	G_aux<-function(x) {
                return(G(beta=beta,a=a,b=b,c=c,s=s,t=t,x[1],x[2]))#---t_1 parametro de h
              }
         #return(integral2(G_aux,0,D_1,0,D_2,reltol = tol*10^2,vectorized=FALSE)$Q)
         
         return(pcubature(G_aux, c(0, 0), c(D1, D2),tol=tol)$integral)
} 



#------Covariance function of wsfmOU

cov_OU<-function(time,beta,sigma,a,b,c)
{
	n<-length(time)
	K<-matrix(rep(0,n*n),n,n)
	B<-matrix(rep(0,n*n),n,n)
	M_1<-matrix(rep(0,n*n),n,n)
    M_2<-matrix(rep(0,n*n),n,n)
    C<-cov_wfbm(time,a,b,c)
    D<-rep(0,n)
    D[1]<-time[1]
    D[-1]<-diff(time)
    
    for(i in 1:n) {
     for(j in 1:i) {
       M_2[i,j]<-G_aux_OU(beta,a,b,c,time[i],time[j],D[i],D[j])
       M_2[j,i]<-M_2[i,j]
       M_1[i,j]<-H_aux_OU(beta,a,b,c,time[i],time[j],D[i])
       M_1[j,i]<-H_aux_OU(beta,a,b,c,time[j],time[i],D[j])
       B[i,j]<-exp(-beta*(time[i]-time[j]))
       } 
       
     }
     R<-(sigma*sigma*beta*beta)*M_2
     W_2<-(sigma*sigma*beta)*(B%*%M_1)
     K<-(sigma*sigma)*C+B%*%R%*%t(B)-(W_2+t(W_2))
     #K<-(sigma*sigma)*C+K
     return(K)
} 




#-------simulations

T<-50
n<-200
time<-sort(c(runif(n-1,0,T),T))
D<-T/n
time<-seq(D,T,length=n)
sigma<-4.2
beta<-3.7
b<-1
a<--0.8
c<-1


t <- proc.time()
K<-cov_OU(time,beta,sigma,a,b,c)
proc.time()-t




mu_i_1<-0
mu_1<-rep(0,n)
for(i in 1:n){
 mu_1[i]<-mu_i_1
}
sim_lon<-mvrnorm(  1, mu_1, K )
plot(c(0,time),c(mu_i_1,sim_lon), type="l",xlab="t",ylab=expression(v["f,b,t"]),lwd=2,cex.main=2,cex.lab=1.2)




diagonal<-rep(0,n)
for(i in 1:n){
	diagonal[i]<-K[i,i]
}

plot(time,diagonal,type="l")




#------End wsfBmOU



#--------------Goemetric wsfBm------------
#----simulation
T<-10
n<-1000
D<-T/n
b<-1.14
a<-1.6
c<-0
mu<-1.34
sigma<-1.71
S_ini<-1
time<-seq(D,T,length=n)
sim<-as.numeric(simulation(time,a,b,c)[1,])


X<-(mu-sigma*sigma/2)*time+sigma*sim
S<-exp(X)

plot(c(0,time),c(S_ini,S), type="l",xlab="t",ylab=expression(S["t,f,b"]),lwd=2,cex.main=2,cex.lab=1.2)



#----Put diferent function en Goemetric wsfBm

D<-function(u,s,t,b) {#----Delta function
   return( (1/(1-b)) *(cos(u/(1+u)))*(  (t-u)^b+(s-u)^b-(t+s-2*u)^b ) ) 
} 


covariance_function_2<-function(s,t,b){
    		     sapply(min(s,t),function(y){
    		 	      g<-function(z){
                         return(D(z,s=s,t=t,b=b))#---t_1 parametro de h
                     }
                     return(integrate(g,0,y)$val)
                 }
                )	
		      }


cov_wfbm_2<-function(time,b){
  n<-length(time)
  K<-matrix(rep(0,n*n),n,n)
    for(i in 1:n) {
      for(j in 1:i) {
        K[i,j]<-covariance_function_2(time[i],time[j],b)
        K[j,i]<-K[i,j]
      } 
    }
  return(K) 
 } 


simulation_2<-function(time,b){
	n<-length(time)
	mean<-rep(0,n)
	K<-cov_wfbm_2(time,b)
return(rmvnorm(1,mean,K))	
}

sim<-as.numeric(simulation_2(time,b)[1,])


X<-(mu-sigma*sigma/2)*time+sigma*sim
S<-exp(X)

plot(c(0,time),c(S_ini,S), type="l",xlab="t",ylab=expression(S["t,f,b"]),lwd=2,cex.main=2,cex.lab=1.2)




#------------------------





#--------Geberalizacion to R^d wsfBm




periodic_kernel<-function(d,sigma,beta,rho){
	return(sigma*sigma*exp(-2*sin(pi*d/rho)^2/(beta*beta)))
}


convarinzac_periodic_kernel<-function(x,y,sigma,beta,rho,alpha,c){
	d<-length(x)
	dist<-norm(x,y)
	cero<-rep(0,d)
	t<-norm(cero,x)
	s<-norm(cero,y)
	if(min(s,t)>1){
		if(c==0){
	               return(2*(pi^(d/2))/(gamma(d/2))*(alpha+d)*(min(t,s)^(alpha+d)-1)*periodic_kernel(dist,sigma,beta,rho) )
	         }
	     else{
	     	if(alpha<0){
	     		return(2*(pi^(d/2))/(gamma(d/2)*((-alpha)^(d)))*(gammainc(d,-alpha)-gammainc(d,-alpha*min(t,s)))*periodic_kernel(dist,sigma,beta,rho) )
	     	}
	     	else{ #---alpha>0
	     		alpha
	     	}
	     }      
	}
	else{
		return(0)
	}
}









rotational_kernel<-function(d,rho,kappa){
	return((1+d*d/(2*rho*kappa^2))^(-rho))
}


convarinzac_rotational_kernel<-function(x,y,rho,kappa,alpha,c){
	d<-length(x)
	dist<-norm(x,y)
	cero<-rep(0,d)
	t<-norm(cero,x)
	s<-norm(cero,y)
	if(min(s,t)>1){
		if(c==0){
	               return(2*(pi^(d/2))/(gamma(d/2))*(alpha+d)*(min(t,s)^(alpha+d)-1)*rotational_kernel(dist, rho, kappa) )
	         }
	     else{
	     	if(alpha<0){
	     		return(2*(pi^(d/2))/(gamma(d/2)*((-alpha)^(d)))*(gammainc(d,-alpha)-gammainc(d,-alpha*min(t,s)))*rotational_kernel(dist, rho, kappa) )
	     	}
	     	else{ #---alpha>0
	     		alpha
	     	}
	     }      
	}
	else{
		return(0)
	}
}



dexponential_kernel<-function(d,sigma,beta){
	return((sigma^2)*exp(-d*d*beta/2))
}


convarinzac_dexponential_kernel<-function(x,y,sigma,beta,alpha,c){
	d<-length(x)
	dist<-norm(x,y)
	cero<-rep(0,d)
	t<-norm(cero,x)
	s<-norm(cero,y)
	if(min(s,t)>1){
		if(c==0){
	               return(2*(pi^(d/2))/(gamma(d/2))*(alpha+d)*(min(t,s)^(alpha+d)-1)*dexponential_kernel(dist, sigma, beta) )
	         }
	     else{
	     	if(alpha<0){
	     		return(2*(pi^(d/2))/(gamma(d/2)*((-alpha)^(d)))*(gammainc(d,-alpha)-gammainc(d,-alpha*min(t,s)))*dexponential_kernel(dist, sigma, beta) )
	     	}
	     	else{ #---alpha>0
	     		alpha
	     	}
	     }      
	}
	else{
		return(0)
	}
}




convarinzac_matter_dim<-function(x,y,rho,kappa,alpha,c){
	d<-length(x)
	dist<-norm(x,y)
	cero<-rep(0,d)
	t<-norm(cero,x)
	s<-norm(cero,y)
	if(min(s,t)>1){
		if(c==0){
	               return(2*(pi^(d/2))/(gamma(d/2))*(alpha+d)*(min(t,s)^(alpha+d)-1)*matern.kernel(dist, rho, kappa) )
	         }
	     else{
	     	if(alpha<0){
	     		return(2*(pi^(d/2))/(gamma(d/2)*((-alpha)^(d)))*(gammainc(d,-alpha)-gammainc(d,-alpha*min(t,s)))*matern.kernel(dist, rho, kappa) )
	     	}
	     	else{ #---alpha>0
	     		alpha
	     	}
	     }      
	}
	else{
		return(0)
	}
}





Integral_1<-function(sig,x,y,H,alpha,r,theta){
	aux<-0
	aux_2<-0
	u<-rep(0,2)
	u[1]<-r*cos(theta)
	u[2]<-r*sin(theta)
	aux_2<-norm(x,u)^(2*H)+norm(y,u)^(2*H)-norm(x+y,2*u)^(2*H)
	 if(sig==-1){
	 	aux<-norm(x,u)^(2*H)+norm(y,u)^(2*H)-norm(x,y)^(2*H)
	 	return((r^(alpha+1))*aux)
	 	}
	 else{
	 	aux_2<-norm(x,u)^(2*H)+norm(y,u)^(2*H)-norm(x+y,2*u)^(2*H)
	 	return((r^(alpha+1))*aux_2)
	 	}
}


Integral_2<-function(sig,x,y,H,alpha,r,theta){
	aux<-0
	aux_2<-0
	u<-rep(0,2)
	u[1]<-r*cos(theta)
	u[2]<-r*sin(theta)
	if(sig==-1){
		aux<-norm(x,u)^(2*H)+norm(y,u)^(2*H)-norm(x,y)^(2*H)
		return(exp(alpha*r)*r*aux)
		}
	else{
		aux_2<-norm(x,u)^(2*H)+norm(y,u)^(2*H)-norm(x+y,2*u)^(2*H)
		return(exp(alpha*r)*r*aux_2)
		}
	}



tol<-1e-4


Integral_11<-function(sig,x,y,H,alpha)
{
	
	t<-norm(x,c(0,0))
	s<-norm(y,c(0,0))
	if(min(s,t)>1){
	G_aux<-function(x) {
                return(Integral_1(sig=sig,x=x,y=y,H=H,alpha=alpha,x[1],x[2]))#---t_1 parametro de h
              }
         #return(integral2(G_aux,0,D_1,0,D_2,reltol = tol*10^2,vectorized=FALSE)$Q)
         
         return(pcubature(G_aux, c(1, 0), c(min(t,s), 2*pi),tol=tol)$integral)
         }
      else{return(0)}   
} 



Q_H<-function(sig,x,y,H){
	
	if(sig==-1){return(norm(x,c(0,0))^(2*H)+norm(y,c(0,0))^(2*H)-norm(x,y)^(2*H))}
	else{return(norm(x,c(0,0))^(2*H)+norm(y,c(0,0))^(2*H)-norm(x,-1*y)^(2*H))}
}


Integral_21<-function(sig,x,y,H,alpha)
{
	
	t<-norm(x,c(0,0))
	s<-norm(y,c(0,0))
	if(min(s,t)>1){
	G_aux_2<-function(x) {
                return(Integral_2(sig=sig,x=x,y=y,H=H,alpha=alpha,x[1],x[2]))#---t_1 parametro de h
              }
         #return(integral2(G_aux,0,D_1,0,D_2,reltol = tol*10^2,vectorized=FALSE)$Q)
         
         return(pcubature(G_aux_2, c(1, 0), c(min(t,s), 2*pi),tol=tol)$integral)
         }
      else{return(0)}   
} 











#----Matern

#-----Parmeter Matern.  1-4
H<-0.78
sig<-1
rho<-2.1
kappa<-4.3
alpha<-0.92
alpha_2<-0.1
alpha_3<--2.4

H_2<-0.3



#------Rotational.   5-6
#-----Parmeter Rotational
sigma<-1
rho_r<-2.1
kappa_r<-4.3
alpha_r<-0.54
alpha_2_r<-0.1
alpha_3_r<--0.9
H_r<-0.78
H_2_r<-0.3



#------Doble exponential          7
#-----Parmeter Doble exponencial
sigma_e<-0.72
beta_e<-8.4
alpha_e<-0.54
alpha_2_e<-0.1
alpha_3_e<--0.9
H_e<-0.78
H_2_e<-0.3




#------periodic
#-----Parmeter periodic
sigma_p<-1.31
beta_p<-1.3
rho_p<-2
alpha_p<-0.54
alpha_2_p<-0.1
alpha_3_p<--0.9
H_p<-0.78
H_2_p<-0.3



block<-100
reg_a<-seq(-2,2.3,length=block)
reg_b<-seq(-2,2.3,length=block)
point<-c(1,1)
profile<-matrix(rep(0,block*block),block,block)
profile_2<-matrix(rep(0,block*block),block,block)
profile_3<-matrix(rep(0,block*block),block,block)
profile_4<-matrix(rep(0,block*block),block,block)
profile_5<-matrix(rep(0,block*block),block,block)
profile_6<-matrix(rep(0,block*block),block,block)
profile_7<-matrix(rep(0,block*block),block,block)
profile_8<-matrix(rep(0,block*block),block,block)
for(i in 1:block){
 for(j in 1:block){
   dist<-norm(c(reg_a[i],reg_b[j]),point)
  profile[i,j]<-convarinzac_matter_dim(c(reg_a[i],reg_b[j]),point,rho,kappa,alpha,0)+Integral_21(sig,c(reg_a[i],reg_b[j]),point,H,alpha_2)
  profile_2[i,j]<-convarinzac_matter_dim(c(reg_a[i],reg_b[j]),point,rho,kappa,alpha,0)+Integral_21(-sig,c(reg_a[i],reg_b[j]),point,H,alpha_2)
  profile_3[i,j]<-convarinzac_matter_dim(c(reg_a[i],reg_b[j]),point,rho,kappa,alpha_3,1)
  profile_4[i,j]<-Integral_11(sig,c(reg_a[i],reg_b[j]),point,H_2,alpha+7.42)+Integral_11(sig,c(reg_a[i],reg_b[j]),point,H,alpha-0.16)
  profile_5[i,j]<-convarinzac_rotational_kernel(c(reg_a[i],reg_b[j]),point,rho_r,kappa_r,alpha_r,0)+Integral_21(sig,c(reg_a[i],reg_b[j]),point,H_r,alpha_2_r)
  profile_6[i,j]<-convarinzac_rotational_kernel(c(reg_a[i],reg_b[j]),point,rho_r,kappa_r,alpha_r,0)+Integral_21(-sig,c(reg_a[i],reg_b[j]),point,H_r,alpha_2_r)
  profile_7[i,j]<-convarinzac_dexponential_kernel(c(reg_a[i],reg_b[j]),point,sigma_e,beta_e,alpha_e,0)+Integral_21(sig,c(reg_a[i],reg_b[j]),point,H_e,alpha_2_e)
  profile_8[i,j]<-convarinzac_periodic_kernel(c(reg_a[i],reg_b[j]),point,sigma_p,beta_p,rho_p,alpha_p,0)+Integral_21(sig,c(reg_a[i],reg_b[j]),point,H_p,alpha_2_p)

 }
}









# Example data for the first plot
reg_a1 <- reg_a
reg_b1 <- reg_b
profile1 <- profile

# Example data for the second plot
reg_a2 <- reg_a
reg_b2 <- reg_b
profile2 <-profile_2

# Example data for the three plot
reg_a3 <- reg_a
reg_b3 <- reg_b
profile3 <- profile_3

# Example data for the four plot
reg_a4 <- reg_a
reg_b4 <- reg_b
profile4 <-profile_4


# Example data for the first plot
reg_a5 <- reg_a
reg_b5 <- reg_b
profile5 <- profile_5

# Example data for the second plot
reg_a6 <- reg_a
reg_b6 <- reg_b
profile6 <-profile_6

# Example data for the three plot
reg_a7 <- reg_a
reg_b7 <- reg_b
profile7 <- profile_7

# Example data for the four plot
reg_a8 <- reg_a
reg_b8 <- reg_b
profile8 <-profile_8

# Define a color palette
color_palette <- colorRampPalette(c("blue", "green", "yellow", "red"))

# Calculate the colors based on the z values for each plot
z_facet1 <- profile1[-1, -1] + profile1[-1, -ncol(profile1)] + profile1[-nrow(profile1), -1] + profile1[-nrow(profile1), -ncol(profile1)]
filled_colors1 <- color_palette(100)[as.numeric(cut(z_facet1, breaks = 100))]

z_facet2 <- profile2[-1, -1] + profile2[-1, -ncol(profile2)] + profile2[-nrow(profile2), -1] + profile2[-nrow(profile2), -ncol(profile2)]
filled_colors2 <- color_palette(100)[as.numeric(cut(z_facet2, breaks = 100))]

z_facet3 <- profile3[-1, -1] + profile3[-1, -ncol(profile3)] + profile3[-nrow(profile3), -1] + profile3[-nrow(profile3), -ncol(profile3)]
filled_colors3 <- color_palette(100)[as.numeric(cut(z_facet3, breaks = 100))]

z_facet4 <- profile4[-1, -1] + profile4[-1, -ncol(profile4)] + profile4[-nrow(profile4), -1] + profile4[-nrow(profile4), -ncol(profile4)]
filled_colors4 <- color_palette(100)[as.numeric(cut(z_facet4, breaks = 100))]

z_facet5 <- profile5[-1, -1] + profile5[-1, -ncol(profile5)] + profile5[-nrow(profile5), -1] + profile5[-nrow(profile5), -ncol(profile5)]
filled_colors5 <- color_palette(100)[as.numeric(cut(z_facet5, breaks = 100))]

z_facet6 <- profile6[-1, -1] + profile6[-1, -ncol(profile6)] + profile6[-nrow(profile6), -1] + profile6[-nrow(profile6), -ncol(profile6)]
filled_colors6 <- color_palette(100)[as.numeric(cut(z_facet6, breaks = 100))]

z_facet7 <- profile7[-1, -1] + profile7[-1, -ncol(profile7)] + profile7[-nrow(profile7), -1] + profile7[-nrow(profile7), -ncol(profile7)]
filled_colors7 <- color_palette(100)[as.numeric(cut(z_facet7, breaks = 100))]

z_facet8 <- profile8[-1, -1] + profile8[-1, -ncol(profile8)] + profile8[-nrow(profile8), -1] + profile8[-nrow(profile8), -ncol(profile8)]
filled_colors8 <- color_palette(100)[as.numeric(cut(z_facet8, breaks = 100))]

# Open PDF device
pdf("8_cov.pdf", width = 14, height = 14)

# Set up the layout for eight plots with a vertical color bar in the middle
layout(matrix(c(1, 2, 3, 4, 5, 6, 7, 8), nrow = 4, byrow = TRUE), widths = c(4, 4,1))




#------


# Create the first 3D plot using persp
par(mar = c(2, 2, 2, 2))
persp_plot1 <- persp(x = reg_a1, y = reg_b1, z = profile1, col = filled_colors1,
                     xlab = "x", ylab = "y", zlab = "z",
                     theta = 30, phi = 30, expand = 0.5, ticktype = "detailed",
                     main = expression(paste(K[paste("M,",2.1,",",4.3)],"((x,y),p)",C["A,f"],"((x,y),p)",+K["0.78,g,A,+"],"((x,y),p)",",  ", f(u),"=||",u,"||",phantom()^0.92,", ",g(u),"=e",phantom()^-2.4,phantom()^group("|",group("|",u, "|"),"|"))))

# Create the second 3D plot using persp
par(mar = c(2, 2, 2, 2))
persp_plot2 <- persp(x = reg_a2, y = reg_b2, z = profile2, col = filled_colors2,
                     xlab = "x", ylab = "y", zlab = "z",
                     theta = 30, phi = 30, expand = 0.5, ticktype = "detailed",
                     main = expression(paste(K[paste("M,",2.1,",",4.3)],"((x,y),p)",C["A,f"],"((x,y),p)",+K["0.78,g,A,-"],"((x,y),p)",",  ", f(u),"=||",u,"||",phantom()^0.92,", ",g(u),"=e",phantom()^-2.4,phantom()^group("|",group("|",u, "|"),"|"))))

# Create the third 3D plot using persp
par(mar = c(2, 2, 2, 2))
persp_plot3 <- persp(x = reg_a3, y = reg_b3, z = profile3, col = filled_colors3,
                     xlab = "x", ylab = "y", zlab = "z",
                     theta = 30, phi = 30, expand = 0.5, ticktype = "detailed",
                     main = expression(paste(K[paste("M,",2.1,",",4.3)],"((x,y),p)",C["A,f"],"((x,y),p)",",  ", f(u),"=e",phantom()^-2.4,phantom()^group("|",group("|",u, "|"),"|"))))

# Create the fourth 3D plot using persp
par(mar = c(2, 2, 2, 2))
persp_plot4 <- persp(x = reg_a4, y = reg_b4, z = profile4, col = filled_colors4,
                     xlab = "x", ylab = "y", zlab = "z",
                     theta = 30, phi = -50, expand = 0.5, ticktype = "detailed",
                     main = expression(paste(K["0.3,f,A,+"],"((x,y),p)",+K["0.78,g,A,+"],"((x,y),p)",",  ", f(u),"=||",u,"||",phantom()^8.34,", ",g(u),"=||",u,"||",phantom()^0.76)))

# Create the fifth 3D plot using persp
par(mar = c(2, 2, 2, 2))
persp_plot5 <- persp(x = reg_a5, y = reg_b5, z = profile5, col = filled_colors5,
                     xlab = "x", ylab = "y", zlab = "z",
                     theta = 30, phi = 30, expand = 0.5, ticktype = "detailed",
                     main = expression(paste(K[paste("RQ,",1,",",2.1,",",4.3)],"((x,y),p)",C["A,f"],"((x,y),p)",+K["0.78,g,A,+"],"((x,y),p)",",  ", f(u),"=||",u,"||",phantom()^0.54,", ",g(u),"=e",phantom()^0.1,phantom()^group("|",group("|",u, "|"),"|"))))

# Create the sixth 3D plot using persp
par(mar = c(2, 2, 2, 2))
persp_plot6 <- persp(x = reg_a6, y = reg_b6, z = profile6, col = filled_colors6,
                     xlab = "x", ylab = "y", zlab = "z",
                     theta = 30, phi = -50, expand = 0.5, ticktype = "detailed",
                     main = expression(paste(K[paste("RQ,",1,",",2.1,",",4.3)],"((x,y),p)",C["A,f"],"((x,y),p)",+K["0.78,g,A,-"],"((x,y),p)",",  ", f(u),"=||",u,"||",phantom()^0.54,", ",g(u),"=e",phantom()^0.1,phantom()^group("|",group("|",u, "|"),"|"))))

# Create the seventh 3D plot using persp
par(mar = c(2, 2, 2, 2))
persp_plot7 <- persp(x = reg_a7, y = reg_b7, z = profile7, col = filled_colors7,
                     xlab = "x", ylab = "y", zlab = "z",
                     theta = 30, phi = 30, expand = 0.5, ticktype = "detailed",
                     main = expression(paste(K[paste("DE,",0.72,",",8.4)],"((x,y),p)",C["A,f"],"((x,y),p)",+K["0.78,g,A,+"],"((x,y),p)",",  ", f(u),"=||",u,"||",phantom()^0.54,", ",g(u),"=e",phantom()^0.1,phantom()^group("|",group("|",u, "|"),"|"))))

# Create the eighth 3D plot using persp
par(mar = c(2, 2, 2, 2))
persp_plot8 <- persp(x = reg_a8, y = reg_b8, z = profile8, col = filled_colors8,
                     xlab = "x", ylab = "y", zlab = "z",
                     theta = 30, phi = 30, expand = 0.5, ticktype = "detailed",
                     main = expression(paste(K[paste("P,",1.31,",",1.3,",",2)],"((x,y),p)",C["A,f"],"((x,y),p)",+K["0.78,g,A,+"],"((x,y),p)",",  ", f(u),"=||",u,"||",phantom()^0.54,", ",g(u),"=e",phantom()^0.1,phantom()^group("|",group("|",u, "|"),"|"))))

# Add a vertical color bar using the image.plot function
#layout(matrix(c(1, 2), nrow = 1), widths = c(8, 1)) # Adjust the width of the color bar column
#par(mar = c(2, 2, 2, 2))
#image.plot(zlim = range(c(profile1, profile2, profile3, profile4, profile5, profile6, profile7, profile8)), col = color_palette(100), legend.only = TRUE, horizontal = FALSE, legend.shrink = 0.8, legend.width = 1.5, legend.mar = 4.1, axis.args = list(mgp = c(3, 1, 0), tcl = -0.5), legend.lab = "Values", legend.args = list(text = "Values", side = 2, line = 0.5))

# Close the PDF device
dev.off()







# Create the first 3D plot using persp
par(mar = c(2, 2, 2, 2))
persp_plot1 <- persp(x = reg_a1, y = reg_b1, z = profile1, col = filled_colors1,
                     xlab = "x", ylab = "y", zlab = "z",
                     theta = 30, phi = 30, expand = 0.5, ticktype = "detailed",
                     main = expression(paste(K[paste(2.1,",",4.3)],"((x,y),p)",C["A,f"],"((x,y),p)",+K["0.78,g,A,+"],"((x,y),p)",",  ", f(u),"=||",u,"||",phantom()^0.92,", ",g(u),"=e",phantom()^-2.4,phantom()^group("|",group("|",u, "|"),"|"))))

# Create the second 3D plot using persp
par(mar = c(2, 2, 2, 2))
persp_plot2 <- persp(x = reg_a2, y = reg_b2, z = profile2, col = filled_colors2,
                     xlab = "x", ylab = "y", zlab = "z",
                     theta = 30, phi = 30, expand = 0.5, ticktype = "detailed",
                     main = expression(paste(K[paste(2.1,",",4.3)],"((x,y),p)",C["A,f"],"((x,y),p)",+K["0.78,g,A,-"],"((x,y),p)",",  ", f(u),"=||",u,"||",phantom()^0.92,", ",g(u),"=e",phantom()^-2.4,phantom()^group("|",group("|",u, "|"),"|"))))

# Create the third 3D plot using persp
par(mar = c(2, 2, 2, 2))
persp_plot3 <- persp(x = reg_a3, y = reg_b3, z = profile3, col = filled_colors3,
                     xlab = "x", ylab = "y", zlab = "z",
                     theta = 30, phi = 30, expand = 0.5, ticktype = "detailed",
                     main =  expression(paste(K[paste(2.1,",",4.3)],"((x,y),p)",C["A,f"],"((x,y),p)",",  ", f(u),"=e",phantom()^-2.4,phantom()^group("|",group("|",u, "|"),"|"))))

# Create the fourth 3D plot using persp
par(mar = c(2, 2, 2, 2))
persp_plot4 <- persp(x = reg_a4, y = reg_b4, z = profile4, col = filled_colors4,
                     xlab = "x", ylab = "y", zlab = "z",
                     theta = 30, phi = -50, expand = 0.5, ticktype = "detailed",
                     main = expression(paste(K["0.3,f,A,+"],"((x,y),p)",+K["0.78,g,A,+"],"((x,y),p)",",  ", f(u),"=||",u,"||",phantom()^8.34,", ",g(u),"=||",u,"||",phantom()^0.76)))

# Add a vertical color bar using the image.plot function
#layout(matrix(c(1, 2), nrow = 1), widths = c(8, 2)) 
# Adjust the width of the color bar column 
#par(mar = c(2, 2, 2, 2))
#image.plot(zlim = range(c(profile1, profile2, profile3, profile4)), col = color_palette(100), legend.only = TRUE, horizontal = TRUE, legend.shrink = 0.8, legend.width = 1.5, legend.mar = 4.1, axis.args = list(mgp = c(3, 1, 0), tcl = -0.5),legend.lab = "Values", legend.args = list(text = "Values", side = 2, line = 0.5)) 
# Close the PDF device 
dev.off()


